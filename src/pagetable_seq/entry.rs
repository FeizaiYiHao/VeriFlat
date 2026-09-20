use vstd::prelude::*;
verus! {

// use vstd::ptr::PointsTo;
use crate::*;

// use crate::array::*;

#[derive(Debug)]
pub struct PageEntryPerm {
    pub present: bool,
    pub ps: bool,
    pub write: bool,
    pub execute_disable: bool,
    pub user: bool,
    pub kernel_present: bool,
}

impl Clone for PageEntryPerm {
    fn clone(&self) -> (ret:Self) 
        ensures
            self == ret,
    {
        PageEntryPerm {
            present: self.present,
            ps: self.ps,
            write: self.write,
            execute_disable: self.execute_disable,
            user: self.user,
            kernel_present: self.kernel_present,
        }
    }

}

#[derive(Debug)]
pub struct PageEntry {
    pub addr: PAddr,
    pub perm: PageEntryPerm,
    // pub ps: bool,
}
impl Clone for PageEntry {
    fn clone(&self) -> (ret:Self) 
        ensures
            self == ret,
    {
        PageEntry {
            addr: self.addr,
            perm: self.perm.clone(),
        }
    }

}
impl PageEntry {
    pub open spec fn is_empty(&self) -> bool {
        &&& self.addr == 0
        &&& self.perm.present == false
        &&& self.perm.ps == false
        &&& self.perm.write == false
        &&& self.perm.execute_disable == false
        &&& self.perm.user == false
        &&& self.perm.kernel_present == false
    }

    pub fn empty() -> (ret: Self)
        ensures
            ret.is_empty(),
    {
        PageEntry {
            addr: 0,
            perm: PageEntryPerm {
                present: false,
                ps: false,
                write: false,
                execute_disable: false,
                user: false,
                kernel_present: false,
            },
        }
    }
}

pub struct MapEntry {
    pub addr: PAddr,
    pub write: bool,
    pub execute_disable: bool,
    pub present: bool,
    pub owning_container: Ghost<RwLockContainerPtr>,
}

pub struct TLBEntry {
    pub addr: PAddr,
    pub write: bool,
    pub execute_disable: bool,
}

pub open spec fn spec_page_entry_to_map_entry(
    p: &PageEntry,
    owning_container: Ghost<RwLockContainerPtr>,
) -> MapEntry {
    MapEntry {
        addr: p.addr,
        write: p.perm.write,
        execute_disable: p.perm.execute_disable,
        present: p.perm.present,
        owning_container,
    }
}

#[verifier(when_used_as_spec(spec_page_entry_to_map_entry))]
pub fn page_entry_to_map_entry(
    p: &PageEntry,
    owning_container: Ghost<RwLockContainerPtr>,
) -> (ret: MapEntry)
    ensures
        ret =~= spec_page_entry_to_map_entry(p, owning_container),
{
    MapEntry {
        addr: p.addr,
        write: p.perm.write,
        execute_disable: p.perm.execute_disable,
        present: p.perm.present,
        owning_container,
    }
}


// pub open spec fn spec_map_entry_to_page_entry(m: &MapEntry, ps: bool) -> PageEntry {
//     PageEntry {
//         addr: m.addr,
//         perm: PageEntryPerm {
//             present: true,
//             ps: ps,
//             write: m.write,
//             execute_disable: m.execute_disable,
//             user: true,
//             present: m.present,
//         },
//     }
// }

// #[verifier(when_used_as_spec(spec_map_entry_to_page_entry))]
// pub fn map_entry_to_page_entry(m: &MapEntry, ps: bool) -> (ret: PageEntry)
//     ensures
//         ret == spec_map_entry_to_page_entry(m, ps),
// {
//     PageEntry {
//         addr: m.addr,
//         perm: PageEntryPerm {
//             present: true,
//             ps: ps,
//             write: m.write,
//             execute_disable: m.execute_disable,
//             user: true,
//             present: m.present,
//         },
//     }
// }

pub open spec fn usize2present(v: usize) -> bool {
    (v & PAGE_ENTRY_PRESENT_MASK as usize) != 0
}

pub open spec fn usize2ps(v: usize) -> bool {
    (v & PAGE_ENTRY_PS_MASK as usize) != 0
}

pub open spec fn usize2write(v: usize) -> bool {
    (v & PAGE_ENTRY_WRITE_MASK as usize) != 0
}

pub open spec fn usize2execute_disable(v: usize) -> bool {
    (v & PAGE_ENTRY_EXECUTE_MASK as usize) != 0
}

pub open spec fn usize2user(v: usize) -> bool {
    (v & PAGE_ENTRY_USER_MASK as usize) != 0
}

pub open spec fn usize2kernel_present(v: usize) -> bool {
    (v & PAGE_ENTRY_KERNEL_PRESENT_MASK as usize) != 0
}

pub proof fn zero_leads_is_empty_page_entry()
    ensures
        spec_usize2page_entry(0).is_empty(),
{
    assert(spec_usize2page_entry(0).is_empty()) by (compute);
}

pub proof fn mem_valid_zero()
    ensures
        mem_valid(0),
{
    assert(0usize & (!0x0000_ffff_ffff_f000u64) as usize == 0) by (compute);
}

pub open spec fn spec_usize2page_entry_perm(v: usize) -> PageEntryPerm {
    PageEntryPerm {
        present: usize2present(v),
        ps: usize2ps(v),
        write: usize2write(v),
        execute_disable: usize2execute_disable(v),
        user: usize2user(v),
        kernel_present: usize2kernel_present(v),
    }
}

#[verifier(when_used_as_spec(spec_usize2page_entry_perm))]
pub fn usize2page_entry_perm(v: usize) -> (ret: PageEntryPerm)
    ensures
        ret =~= spec_usize2page_entry_perm(v),
{
    PageEntryPerm {
        present: (v & PAGE_ENTRY_PRESENT_MASK as usize) != 0,
        ps: (v & PAGE_ENTRY_PS_MASK as usize) != 0,
        write: (v & PAGE_ENTRY_WRITE_MASK as usize) != 0,
        execute_disable: (v & PAGE_ENTRY_EXECUTE_MASK as usize) != 0,
        user: (v & PAGE_ENTRY_USER_MASK as usize) != 0,
        kernel_present: (v & PAGE_ENTRY_KERNEL_PRESENT_MASK as usize) != 0,
    }
}

pub open spec fn spec_usize2page_entry(v: usize) -> PageEntry {
    PageEntry { addr: usize2pa(v), perm: usize2page_entry_perm(v) }
}

#[verifier(when_used_as_spec(spec_usize2page_entry))]
pub fn usize2page_entry(v: usize) -> (ret: PageEntry)
    ensures
        ret =~= spec_usize2page_entry(v),
{
    PageEntry { addr: usize2pa(v), perm: usize2page_entry_perm(v) }
}

pub open spec fn spec_usize2pa(v: usize) -> PAddr {
    v & MEM_MASK as usize
}

pub proof fn spec_usize2pa_mem_valid(v: usize)
    ensures
        mem_valid(spec_usize2pa(v)),
{
    assert(spec_usize2pa(v) & (!0x0000_ffff_ffff_f000u64) as usize == 0)
        by (bit_vector);
}

#[verifier(when_used_as_spec(spec_usize2pa))]
pub fn usize2pa(v: usize) -> (ret: PAddr)
    ensures
        ret =~= spec_usize2pa(v),
        mem_valid(ret),
{
    let ret = v & MEM_MASK as usize;
    proof {
        spec_usize2pa_mem_valid(v);
    }
    return ret;
}

pub fn page_entry2usize(page_entry: &PageEntry) -> (ret: usize)
    requires
        mem_valid(page_entry.addr),
    ensures
        usize2pa(ret) == page_entry.addr,
        usize2page_entry_perm(ret) =~= page_entry.perm,
{
    let addr = page_entry.addr;
    let present = page_entry.perm.present;
    let ps = page_entry.perm.ps;
    let write = page_entry.perm.write;
    let execute_disable = page_entry.perm.execute_disable;
    let user = page_entry.perm.user;
    let kernel_present = page_entry.perm.kernel_present;
    let ret = addr
        | if present { PAGE_ENTRY_PRESENT_MASK as usize } else { 0 }
        | if ps { PAGE_ENTRY_PS_MASK as usize } else { 0 }
        | if write { PAGE_ENTRY_WRITE_MASK as usize } else { 0 }
        | if execute_disable { PAGE_ENTRY_EXECUTE_MASK as usize } else { 0 }
        | if user { PAGE_ENTRY_USER_MASK as usize } else { 0 }
        | if kernel_present { PAGE_ENTRY_KERNEL_PRESENT_MASK as usize } else { 0 };
    assert({
        &&& ret & MEM_MASK as usize == addr
        &&& (ret & PAGE_ENTRY_PRESENT_MASK as usize != 0) == present
        &&& (ret & PAGE_ENTRY_PS_MASK as usize != 0) == ps
        &&& (ret & PAGE_ENTRY_WRITE_MASK as usize != 0) == write
        &&& (ret & PAGE_ENTRY_EXECUTE_MASK as usize != 0) == execute_disable
        &&& (ret & PAGE_ENTRY_USER_MASK as usize != 0) == user
        &&& (ret & PAGE_ENTRY_KERNEL_PRESENT_MASK as usize != 0) == kernel_present
    }) by (bit_vector)
        requires
            addr & (!MEM_MASK) as usize == 0,
            ret == addr
                | if present { PAGE_ENTRY_PRESENT_MASK as usize } else { 0 }
                | if ps { PAGE_ENTRY_PS_MASK as usize } else { 0 }
                | if write { PAGE_ENTRY_WRITE_MASK as usize } else { 0 }
                | if execute_disable { PAGE_ENTRY_EXECUTE_MASK as usize } else { 0 }
                | if user { PAGE_ENTRY_USER_MASK as usize } else { 0 }
                | if kernel_present { PAGE_ENTRY_KERNEL_PRESENT_MASK as usize } else { 0 },
    ;
    ret
}

} // verus!
