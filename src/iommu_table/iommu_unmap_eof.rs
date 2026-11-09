use vstd::prelude::*;
verus! {
use crate::*;
use super::entry::*;
use super::page_map::*;

impl IommuTable {
    /// Operation-state summary of `unmap_4k_page_user_view`: entry `target_l1i` of the L1 map `target_l1_p` loses its present bit and the kernel 4K mapping of its address is kept with `present` cleared; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn unmap_4k_page_user_view_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr) -> bool {
        &&& post == (Self { l1_tables: post.l1_tables, mapping_4k: post.mapping_4k, ..pre })
        &&& post.l1_tables.view().dom() == pre.l1_tables.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.l1_tables.view().spec_index(p)] pre.l1_tables.view().dom().contains(p) && p != target_l1_p ==> post.l1_tables.view().spec_index(p) == pre.l1_tables.view().spec_index(p)
        &&& post.l1_tables.view().spec_index(target_l1_p).addr() == target_l1_p
        &&& post.l1_tables.view().spec_index(target_l1_p).is_init()
        &&& post.l1_tables.view().spec_index(target_l1_p).value().iommu_wf()
        &&& forall|i: usize| #![trigger post.l1_tables.view().spec_index(target_l1_p).value().spec_index(i)] pei_valid(i) && i != target_l1i ==> post.l1_tables.view().spec_index(target_l1_p).value().spec_index(i) =~= pre.l1_tables.view().spec_index(target_l1_p).value().spec_index(i)
        &&& post.l1_tables.view().spec_index(target_l1_p).value().spec_index(target_l1i)
            =~= (PageEntry { perm: PageEntryPerm { present: false, write: false, ..pre.l1_tables.view().spec_index(target_l1_p).value().spec_index(target_l1i).perm }, ..pre.l1_tables.view().spec_index(target_l1_p).value().spec_index(target_l1i) })
        &&& post.mapping_4k() == pre.mapping_4k().insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)), MapEntry { present: false, ..pre.mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) })
    }

    /// EOF closure of `unmap_4k_page_user_view`: every page-table invariant leaf.
    pub(super) proof fn unmap_4k_page_user_view_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is Some || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) == true,
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf(),
            post.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is Some,
            !post.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i)->0.perm.present,
            !post.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i)->0.perm.write,
    {
        assert(pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)))) by { reveal(IommuTable::wf_mapping_4k); };
        Self::unmap_4k_page_user_view_eof_wf_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_wf_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_disjoint_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_disjoint_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        assert(post.wf_mapping_2m()) by { reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing); reveal(IommuTable::wf_mapping_2m); };
        assert(post.wf_mapping_1g()) by { reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing); reveal(IommuTable::wf_mapping_1g); };
        Self::unmap_4k_page_user_view_eof_user_only(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_kernel_entries_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_va_addr_valid_and_pcid_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        post.wf_mapping_4k_at(target_l4i, target_l3i, target_l2i, target_l1i);
    }

    /// EOF closure of `unmap_4k_page_user_view`: `wf_l4`.
    proof fn unmap_4k_page_user_view_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l4(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.wf_l4()) by { reveal(IommuTable::wf_l4); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `wf_l3`.
    proof fn unmap_4k_page_user_view_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l3(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(IommuTable::wf_l3); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `wf_l2`.
    proof fn unmap_4k_page_user_view_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l2(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.wf_l2()) by { reveal(IommuTable::wf_l2); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `wf_l1`.
    proof fn unmap_4k_page_user_view_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l1(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(IommuTable::wf_l1); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `disjoint_l4`.
    proof fn unmap_4k_page_user_view_eof_disjoint_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.disjoint_l4(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.disjoint_l4()) by { reveal(IommuTable::disjoint_l4); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `disjoint_l3`.
    proof fn unmap_4k_page_user_view_eof_disjoint_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.disjoint_l3(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.disjoint_l3()) by { reveal(IommuTable::disjoint_l3); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `disjoint_l2`.
    proof fn unmap_4k_page_user_view_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.disjoint_l2(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.disjoint_l2()) by { reveal(IommuTable::disjoint_l2); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `wf_mapping_4k`.
    proof fn unmap_4k_page_user_view_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        Self::unmap_4k_page_user_view_eof_wf_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_disjoint_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_disjoint_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        assert(post.wf_mapping_4k()) by {
            reveal(IommuTable::wf_mapping_4k);
            spec_index2va_injective();
            post.resolve_l2_unchanged(&pre);
            broadcast use IommuTable::disjoint_l2_implies_resolve_l2_addr_unique_at, IommuTable::wf_l2_implies_resolve_l2_target_in_l1_rev_map_at;
        };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `user_only`.
    proof fn unmap_4k_page_user_view_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.user_only(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.user_only()) by { reveal(IommuTable::user_only); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `rwx_upper_level_entries`.
    proof fn unmap_4k_page_user_view_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.rwx_upper_level_entries()) by { reveal(IommuTable::rwx_upper_level_entries); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `table_pages_wf`.
    proof fn unmap_4k_page_user_view_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.table_pages_wf(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.table_pages_wf()) by { reveal(IommuTable::table_pages_wf); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `tables_reachable_wf`.
    proof fn unmap_4k_page_user_view_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(IommuTable::tables_reachable_wf); post.resolve_l2_unchanged(&pre); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `kernel_entries_wf`.
    proof fn unmap_4k_page_user_view_eof_kernel_entries_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.kernel_entries_wf(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.kernel_entries_wf()) by { reveal(IommuTable::kernel_entries_wf); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `va_addr_valid`, `pcid_wf`, and `did_wf`.
    proof fn unmap_4k_page_user_view_eof_va_addr_valid_and_pcid_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.va_addr_valid(),
            post.pcid_wf(),
            post.did_wf(),
    {
        reveal(IommuTable::unmap_4k_page_user_view_eof_transition_framing);
    }
}
} // verus!
