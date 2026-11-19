use vstd::prelude::*;
verus! {
use crate::*;
use super::entry::*;
use super::page_map::*;

impl IommuTable {
    /// Operation-state summary of `unmap_4k_page_kernel`: entry `target_l1i` of the L1 map `target_l1_p` is cleared and the kernel 4K mapping of its address is removed; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn unmap_4k_page_kernel_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr) -> bool {
        &&& post == (Self { l1_tables: post.l1_tables, mapping_4k: post.mapping_4k, ..pre })
        &&& post.l1_tables.view().dom() == pre.l1_tables.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.l1_tables.view().spec_index(p)] pre.l1_tables.view().dom().contains(p) && p != target_l1_p ==> post.l1_tables.view().spec_index(p) == pre.l1_tables.view().spec_index(p)
        &&& post.l1_tables.view().spec_index(target_l1_p).addr() == target_l1_p
        &&& post.l1_tables.view().spec_index(target_l1_p).is_init()
        &&& post.l1_tables.view().spec_index(target_l1_p).value().iommu_wf()
        &&& forall|i: usize| #![trigger post.l1_tables.view().spec_index(target_l1_p).value().spec_index(i)] pei_valid(i) && i != target_l1i ==> post.l1_tables.view().spec_index(target_l1_p).value().spec_index(i) =~= pre.l1_tables.view().spec_index(target_l1_p).value().spec_index(i)
        &&& post.l1_tables.view().spec_index(target_l1_p).value().spec_index(target_l1i).is_empty()
        &&& post.mapping_4k() == pre.mapping_4k().remove(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)))
    }

    /// EOF closure of `unmap_4k_page_kernel`: every page-table invariant leaf.
    pub(super) proof fn unmap_4k_page_kernel_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf(),
    {
        Self::unmap_4k_page_kernel_eof_wf_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_disjoint_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_disjoint_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        assert(post.wf_mapping_2m()) by { reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing); reveal(IommuTable::wf_mapping_2m); };
        assert(post.wf_mapping_1g()) by { reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing); reveal(IommuTable::wf_mapping_1g); };
        Self::unmap_4k_page_kernel_eof_user_only(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_kernel_entries_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_va_addr_valid_and_pcid_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
    }

    /// EOF closure of `unmap_4k_page_kernel`: `wf_l4`.
    proof fn unmap_4k_page_kernel_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l4(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.wf_l4()) by { reveal(IommuTable::wf_l4); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `wf_l3`.
    proof fn unmap_4k_page_kernel_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l3(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(IommuTable::wf_l3); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `wf_l2`.
    proof fn unmap_4k_page_kernel_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l2(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.wf_l2()) by { reveal(IommuTable::wf_l2); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `wf_l1`.
    proof fn unmap_4k_page_kernel_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l1(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(IommuTable::wf_l1); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `disjoint_l4`.
    proof fn unmap_4k_page_kernel_eof_disjoint_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.disjoint_l4(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.disjoint_l4()) by { reveal(IommuTable::disjoint_l4); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `disjoint_l3`.
    proof fn unmap_4k_page_kernel_eof_disjoint_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.disjoint_l3(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.disjoint_l3()) by { reveal(IommuTable::disjoint_l3); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `disjoint_l2`.
    proof fn unmap_4k_page_kernel_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.disjoint_l2(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.disjoint_l2()) by { reveal(IommuTable::disjoint_l2); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `wf_mapping_4k`.
    proof fn unmap_4k_page_kernel_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_mapping_4k(),
    {
        Self::unmap_4k_page_kernel_eof_wf_mapping_4k_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        reveal(IommuTable::wf_mapping_4k);
    }

    /// EOF closure of `unmap_4k_page_kernel`: the body of `wf_mapping_4k`, stated for each index.
    proof fn unmap_4k_page_kernel_eof_wf_mapping_4k_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger post.mapping_4k.view().spec_index(spec_index2va((l4i,l3i,l2i,l1i)))]
                #![trigger post.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> {
                    &&& post.mapping_4k.view().dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                    &&& post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) is Some
                        ==> post.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).addr == post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.addr
                        && (post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.present ==> post.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).write == post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.write)
                        && post.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).execute_disable == post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.execute_disable
                        && post.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).is_io == post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.is_io
                        && post.mapping_4k.view().spec_index(spec_index2va((l4i, l3i, l2i, l1i))).present == post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)->0.perm.present
                },
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(IommuTable::wf_mapping_4k);
        spec_index2va_injective();
        post.resolve_l2_unchanged(&pre);
        broadcast use IommuTable::disjoint_l2_implies_resolve_l2_addr_unique_at, IommuTable::wf_l2_implies_resolve_l2_target_in_l1_rev_map_at;
    }

    /// EOF closure of `unmap_4k_page_kernel`: `user_only`.
    proof fn unmap_4k_page_kernel_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.user_only(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.user_only()) by { reveal(IommuTable::user_only); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `rwx_upper_level_entries`.
    proof fn unmap_4k_page_kernel_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.rwx_upper_level_entries()) by { reveal(IommuTable::rwx_upper_level_entries); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `table_pages_wf`.
    proof fn unmap_4k_page_kernel_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.table_pages_wf(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.table_pages_wf()) by { reveal(IommuTable::table_pages_wf); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `tables_reachable_wf`.
    proof fn unmap_4k_page_kernel_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(IommuTable::tables_reachable_wf); post.resolve_l2_unchanged(&pre); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `kernel_entries_wf`.
    proof fn unmap_4k_page_kernel_eof_kernel_entries_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.kernel_entries_wf(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.kernel_entries_wf()) by { reveal(IommuTable::kernel_entries_wf); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `va_addr_valid`, `pcid_wf`, and `did_wf`.
    proof fn unmap_4k_page_kernel_eof_va_addr_valid_and_pcid_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L2Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.va_addr_valid(),
            post.pcid_wf(),
            post.did_wf(),
    {
        reveal(IommuTable::unmap_4k_page_kernel_eof_transition_framing);
    }
}
} // verus!
