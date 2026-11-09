use vstd::prelude::*;
verus! {
use crate::*;

pub const IOMMU_READ_MASK: usize = 1;
pub const IOMMU_WRITE_MASK: usize = 2;
pub const IOMMU_HELD_MASK: usize = 1usize << 52;
pub const IOMMU_SOFTWARE_XD_MASK: usize = 1usize << 63;
pub const IOMMU_WORD_MASK: usize = MEM_MASK as usize | IOMMU_READ_MASK | IOMMU_WRITE_MASK | IOMMU_HELD_MASK | IOMMU_SOFTWARE_XD_MASK;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum IommuAccess { Disabled, ReadOnly, ReadWrite }

pub struct IommuEntry {
    pub addr: PAddr,
    pub access: IommuAccess,
    pub held: bool,
    pub software_xd: bool,
}

pub open spec fn iommu_word_valid(raw: usize) -> bool {
    &&& raw & !IOMMU_WORD_MASK == 0
    &&& raw & IOMMU_WRITE_MASK != 0 ==> raw & IOMMU_READ_MASK != 0
}

impl IommuEntry {
    pub open spec fn encoded_word(&self) -> usize {
        self.addr | (match self.access { IommuAccess::Disabled => 0usize, IommuAccess::ReadOnly => 1usize, IommuAccess::ReadWrite => 3usize })
            | (if self.held { IOMMU_HELD_MASK } else { 0 }) | (if self.software_xd { IOMMU_SOFTWARE_XD_MASK } else { 0 })
    }

    /// The shared PageMap view is a bit lens, not a CPU encoding operation.
    pub open spec fn bit_view(&self) -> PageEntry {
        PageEntry { addr: self.addr, perm: PageEntryPerm {
            present: !(self.access is Disabled), ps: false, write: self.access is ReadWrite,
            execute_disable: self.software_xd, user: false, kernel_present: self.held } }
    }

    pub fn encode(&self) -> (raw: usize)
        requires mem_valid(self.addr),
        ensures
            raw == self.encoded_word(),
            iommu_word_valid(raw),
            spec_usize2page_entry(raw) =~= self.bit_view(),
            self.bit_view().is_empty() ==> raw == 0,
    {
        let addr = self.addr;
        let access = match self.access { IommuAccess::Disabled => 0usize, IommuAccess::ReadOnly => 1usize, IommuAccess::ReadWrite => 3usize };
        let held = self.held;
        let xd = self.software_xd;
        let raw = addr | access | if held { IOMMU_HELD_MASK } else { 0 } | if xd { IOMMU_SOFTWARE_XD_MASK } else { 0 };
        assert({
            &&& raw & !IOMMU_WORD_MASK == 0
            &&& raw & 2 != 0 ==> raw & 1 != 0
            &&& raw & MEM_MASK as usize == addr
            &&& (raw & 1 != 0) == (access != 0)
            &&& (raw & PAGE_ENTRY_WRITE_MASK as usize != 0) == (access == 3)
            &&& raw & PAGE_ENTRY_PS_MASK as usize == 0
            &&& raw & PAGE_ENTRY_USER_MASK as usize == 0
            &&& (raw & PAGE_ENTRY_KERNEL_PRESENT_MASK as usize != 0) == held
            &&& (raw & PAGE_ENTRY_EXECUTE_MASK as usize != 0) == xd
            &&& addr == 0 && access == 0 && !held && !xd ==> raw == 0
        }) by (bit_vector)
            requires
                addr & !MEM_MASK as usize == 0,
                access == 0 || access == 1 || access == 3,
                raw == addr | access | if held { IOMMU_HELD_MASK } else { 0 } | if xd { IOMMU_SOFTWARE_XD_MASK } else { 0 },
        ;
        raw
    }

    pub fn from_bit_view(entry: &PageEntry) -> (ret: Self)
        requires
            !entry.perm.ps,
            !entry.perm.user,
            entry.perm.write ==> entry.perm.present,
        ensures ret.bit_view() =~= *entry,
    {
        Self { addr: entry.addr,
            access: if !entry.perm.present { IommuAccess::Disabled } else if entry.perm.write { IommuAccess::ReadWrite } else { IommuAccess::ReadOnly },
            held: entry.perm.kernel_present, software_xd: entry.perm.execute_disable }
    }

    pub fn decode(raw: usize) -> (ret: Self)
        requires iommu_word_valid(raw),
        ensures
            mem_valid(ret.addr),
            ret.bit_view() =~= spec_usize2page_entry(raw),
    {
        let ret = Self { addr: raw & MEM_MASK as usize,
            access: if raw & IOMMU_READ_MASK == 0 { IommuAccess::Disabled } else if raw & IOMMU_WRITE_MASK == 0 { IommuAccess::ReadOnly } else { IommuAccess::ReadWrite },
            held: raw & IOMMU_HELD_MASK != 0, software_xd: raw & IOMMU_SOFTWARE_XD_MASK != 0 };
        assert({
            &&& (raw & MEM_MASK as usize) & !MEM_MASK as usize == 0
            &&& raw & PAGE_ENTRY_PS_MASK as usize == 0
            &&& raw & PAGE_ENTRY_USER_MASK as usize == 0
            &&& (raw & PAGE_ENTRY_WRITE_MASK as usize != 0) == (raw & IOMMU_WRITE_MASK != 0)
        }) by (bit_vector) requires raw & !IOMMU_WORD_MASK == 0;
        ret
    }
}
} // verus!
