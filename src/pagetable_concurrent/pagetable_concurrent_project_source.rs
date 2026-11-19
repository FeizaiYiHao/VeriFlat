use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTableHigher<TABLE_TYPE> {
    pub fn project_4k_source(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, va: VAddr) -> (ret: Option<MapEntry>)
        requires
            (WholePageTable { higher: *self, lower: *lower }).wf(),
            page_table_key_4k_valid::<TABLE_TYPE>(va),
            self.kernel_l4_end <= spec_v2l4index(va),
        ensures
            ret == (WholePageTable { higher: *self, lower: *lower }).spec_project_4k_source(va),
            ret is Some ==> ret->0.present && mapping_4k_target_valid(ret->0.addr, ret->0.is_io),
    {
        let l4i = (va >> 39) & 0x1ff;
        let l3i = (va >> 30) & 0x1ff;
        let l2i = (va >> 21) & 0x1ff;
        let l1i = (va >> 12) & 0x1ff;
        proof {
            let whole = WholePageTable { higher: *self, lower: *lower };
            assert(PAGE_SZ_4K == 4096 && PAGE_SZ_2M == 0x200000 && PAGE_SZ_1G == 0x40000000) by (compute);
            assert(pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                && l4i == spec_v2l4index(va) && l3i == spec_v2l3index(va)
                && l2i == spec_v2l2index(va) && l1i == spec_v2l1index(va)) by (bit_vector)
                requires l4i == (va >> 39) & 0x1ff, l3i == (va >> 30) & 0x1ff,
                    l2i == (va >> 21) & 0x1ff, l1i == (va >> 12) & 0x1ff;
            assert(spec_index2va((l4i, l3i, l2i, l1i)) == va
                && spec_index2va((l4i, l3i, l2i, 0)) == (va / PAGE_SZ_2M * PAGE_SZ_2M) as usize
                && spec_index2va((l4i, l3i, 0, 0)) == (va / PAGE_SZ_1G * PAGE_SZ_1G) as usize
                && va % PAGE_SZ_4K == 0) by (bit_vector)
                requires va & (!MEM_4K_MASK) as usize == 0, l4i == (va >> 39) & 0x1ff,
                    l3i == (va >> 30) & 0x1ff, l2i == (va >> 21) & 0x1ff, l1i == (va >> 12) & 0x1ff;
            whole.wf_mapping_4k_at(l4i, l3i, l2i, l1i);
            whole.wf_mapping_2m_at(l4i, l3i, l2i);
            self.wf_mapping_1g_at(l4i, l3i);
        }
        let l4_entry = match self.get_entry_l4(l4i) { Some(entry) => entry, None => return None };
        let l3_word = self.get_l3_entry_word(l4i, l3i, &l4_entry);
        if l3_word.perm.ps {
            if !l3_word.perm.kernel_present || !l3_word.perm.is_io || !l3_word.perm.present { return None; }
            let addr = l3_word.addr;
            let offset = va % PAGE_SZ_1G;
            proof {
                reveal(io_page_range_valid);
                assert(((addr + offset) as usize) & (!MEM_MASK) as usize == 0 && (addr + offset) as usize % 4096 == 0 && (addr + offset) as usize <= 0x0001_0000_0000_0000usize - 4096usize)
                    by (bit_vector) requires addr <= 0x0001_0000_0000_0000usize - 0x40000000usize, addr % 0x40000000usize == 0, offset == va % 0x40000000usize, va % 4096 == 0;
            }
            let mut source = page_entry_to_map_entry(&l3_word, Ghost(self.mapping_1g.view()[spec_index2va((l4i, l3i, 0, 0))].owning_container.view()));
            source.addr = addr + offset;
            return Some(source);
        }
        if !l3_word.perm.present { return None; }
        if let Some(entry) = self.get_entry_2m_l2(Tracked(lower), l4i, l3i, l2i, &l3_word) {
            if !entry.perm.is_io || !entry.perm.present { return None; }
            let addr = entry.addr;
            let offset = va % PAGE_SZ_2M;
            proof {
                reveal(io_page_range_valid);
                assert(((addr + offset) as usize) & (!MEM_MASK) as usize == 0 && (addr + offset) as usize % 4096 == 0 && (addr + offset) as usize <= 0x0001_0000_0000_0000usize - 4096usize)
                    by (bit_vector) requires addr <= 0x0001_0000_0000_0000usize - 0x200000usize, addr % 0x200000usize == 0, offset == va % 0x200000usize, va % 4096 == 0;
            }
            let mut source = page_entry_to_map_entry(&entry, Ghost(lower.mapping_2m[spec_index2va((l4i, l3i, l2i, 0))].owning_container.view()));
            source.addr = addr + offset;
            return Some(source);
        }
        let l2_entry = match self.get_entry_l2(Tracked(lower), l4i, l3i, l2i, &l3_word) { Some(entry) => entry, None => return None };
        match self.get_entry_l1(Tracked(lower), l4i, l3i, l2i, l1i, &l3_word, &l2_entry) {
            Some(entry) => {
                if !entry.perm.present { return None; }
                Some(page_entry_to_map_entry(&entry, Ghost(lower.mapping_4k[va].owning_container.view())))
            },
            None => None,
        }
    }
    pub fn project_4k_source_range_present(&self, Tracked(lower): Tracked<&PageTableLower<TABLE_TYPE>>, range: &VaRange4K) -> (ret: bool)
        requires
            (WholePageTable { higher: *self, lower: *lower }).wf(),
            range.wf(),
            self.kernel_l4_end <= spec_v2l4index(range.start),
        ensures
            ret == forall|i: int| #![trigger range.view().spec_index(i)] 0 <= i < range.len
                ==> (WholePageTable { higher: *self, lower: *lower }).spec_project_4k_source(range.view().spec_index(i)) is Some,
    {
        let mut i = 0usize;
        while i < range.len
            invariant
                (WholePageTable { higher: *self, lower: *lower }).wf(),
                range.wf(),
                self.kernel_l4_end <= spec_v2l4index(range.start),
                i <= range.len,
                forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < i
                    ==> (WholePageTable { higher: *self, lower: *lower }).spec_project_4k_source(range.view().spec_index(j)) is Some,
            decreases range.len - i,
        {
            let va = range.index(i);
            proof { range.wf_implies_view_index_is_start_plus_offset(); spec_v2l4index_monotonic(range.start, va); }
            if self.project_4k_source(Tracked(lower), va).is_none() { return false; }
            i = i + 1;
        }
        true
    }

}
} // verus!
