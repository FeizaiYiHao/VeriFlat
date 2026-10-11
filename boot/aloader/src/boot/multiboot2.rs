//! Multiboot2.
//!
//! More info: <https://www.gnu.org/software/grub/manual/multiboot2/multiboot.html>

use core::mem;
use core::ptr;
use core::marker::PhantomData;
use core::pin::Pin;

use crate::memory::AcpiMemoryType;
use crate::memory::MemoryRange;
use super::StartInfo;

const TAG_TYPE_NULL: u32 = 0;
const TAG_TYPE_MODULE: u32 = 3;
const TAG_TYPE_MEMORY_INFO: u32 = 4;
const TAG_TYPE_MEMORY_MAP: u32 = 6;

const TAG_ALIGNMENT: usize = 8;

pub struct Multiboot2StartInfo<'a> {
    header: *const Header,
    memory_map: Option<Pin<&'a MemoryMap>>,
}

#[derive(Debug)]
#[repr(C)]
struct Header {
    total_size: u32,
    _reserved: u32,
}

#[derive(Debug)]
#[repr(C)]
struct TagHeader {
    tag_type: u32,
    size: u32,
}

#[derive(Debug)]
#[allow(dead_code)]
enum Tag<'a> {
    MemoryInfo(Pin<&'a MemoryInfo>),
    MemoryMap(Pin<&'a MemoryMap>),
    Module(Pin<&'a Module>),
    Other(u32),
}

#[derive(Debug)]
#[repr(C)]
struct MemoryInfo {
    header: TagHeader,
    mem_lower: u32,
    mem_upper: u32,
}

#[derive(Debug)]
#[repr(C)]
struct MemoryMap {
    header: TagHeader,
    entry_size: u32,
    entry_version: u32,
}

#[derive(Debug)]
#[repr(C)]
struct MemoryMapEntry {
    base_addr: u64,
    length: u64,
    entry_type: AcpiMemoryType,
    _reserved: u32,
}

#[derive(Debug)]
#[repr(C)]
struct Module {
    header: TagHeader,
    mod_start: u32,
    mod_end: u32,
}

#[derive(Debug)]
struct TagIter<'a> {
    cur: *const u8,
    limit: *const u8,
    _lifetime: &'a PhantomData<Header>,
}

#[derive(Debug)]
struct MemoryMapIter<'a> {
    cur: *const u8,
    limit: *const u8,
    entry_size: usize,
    _lifetime: &'a PhantomData<MemoryMap>,
}

impl Header {
    pub fn iter_tags<'a>(&'a self) -> TagIter<'a> {
        TagIter {
            cur: unsafe { self.as_ptr().add(mem::size_of::<Self>() as usize) },
            limit: unsafe { self.as_ptr().add(self.total_size as usize) },
            _lifetime: &PhantomData,
        }
    }

    fn as_ptr(&self) -> *const u8 {
        self as *const _ as *const u8
    }
}

impl TagHeader {
    fn as_ptr(&self) -> *const u8 {
        self as *const _ as *const u8
    }

    fn data<'a>(&'a self) -> Option<Tag<'a>> {
        let p = self.as_ptr();
        unsafe {
            match self.tag_type {
                TAG_TYPE_NULL => None,
                TAG_TYPE_MEMORY_INFO => Some(Tag::MemoryInfo(Pin::new(&*(p as *const _)))),
                TAG_TYPE_MODULE => Some(Tag::Module(Pin::new(&*(p as *const _)))),
                TAG_TYPE_MEMORY_MAP => Some(Tag::MemoryMap(Pin::new(&*(p as *const _)))),
                other => Some(Tag::Other(other)),
            }
        }
    }
}

impl MemoryMap {
    fn data_ptr(self: &Pin<&Self>) -> *const u8 {
        unsafe {
            (self.as_ref().get_ref() as *const Self).add(1) as *const u8
        }
    }

    pub fn entries<'a>(self: &Pin<&'a Self>) -> MemoryMapIter<'a> {
        let self_ptr = self.as_ref().get_ref() as *const Self as *const u8;

        MemoryMapIter {
            cur: self.data_ptr(),
            limit: unsafe { self_ptr.add(self.header.size as usize) },
            entry_size: self.entry_size as usize,
            _lifetime: &PhantomData,
        }
    }
}

impl<'a> Iterator for TagIter<'a> {
    type Item = Tag<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur >= self.limit {
            return None;
        }
        //log::debug!("cur = {:?}, limit = {:?}", self.cur, self.limit);

        let tag_header = unsafe {
            &*(self.cur as *const TagHeader)
        };

        let next = (self.cur as usize + tag_header.size as usize + TAG_ALIGNMENT - 1) & !(TAG_ALIGNMENT - 1);
        self.cur = next as *const _;
        //log::debug!("{:#?}", tag_header);

        tag_header.data()
    }
}

impl<'a> MemoryMapIter<'a> {
    fn null() -> Self {
        Self {
            cur: ptr::null(),
            limit: ptr::null(),
            entry_size: 0,
            _lifetime: &PhantomData,
        }
    }
}

impl<'a> Iterator for MemoryMapIter<'a> {
    type Item = &'a MemoryMapEntry;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur >= self.limit {
            return None;
        }
        //log::debug!("cur = {:?}, limit = {:?}", self.cur, self.limit);

        let entry = unsafe {
            &*(self.cur as *const MemoryMapEntry)
        };

        let next = self.cur as usize + self.entry_size;
        self.cur = next as *const _;
        //log::debug!("{:#?}", tag_header);

        Some(entry)
    }
}

impl Multiboot2StartInfo<'static> {
    pub unsafe fn load(start_info_ptr: *const u8) -> Option<Self> {
        let mut s = Self {
            header: start_info_ptr as *const Header,
            memory_map: None,
        };

        let header = s.header();
        log::info!("{:?}", header);

        for tag in header.iter_tags() {
            if let Tag::MemoryMap(map) = tag {
                s.memory_map = Some(map);
            }
        }

        Some(s)
    }
}

impl<'a> Multiboot2StartInfo<'a> {
    fn header(&self) -> &'a Header {
        unsafe {
            &*(self.header as *const Header)
        }
    }
}

impl<'a> StartInfo for Multiboot2StartInfo<'a> {
    fn iter_memory_regions(
            &self,
        ) -> impl Iterator<Item = (MemoryRange, Option<AcpiMemoryType>)> + '_ {

        let it = if let Some(memory_map) = self.memory_map {
            memory_map.entries()
        } else {
            MemoryMapIter::null()
        };

        it.map(|entry| (MemoryRange::new(entry.base_addr, entry.length), Some(entry.entry_type)))
    }

    fn iter_modlist(&self) -> impl Iterator<Item = MemoryRange> + '_ {
        self.header().iter_tags().filter_map(|tag| {
            if let Tag::Module(module) = tag {
                let length = module.mod_end - module.mod_start;
                Some(MemoryRange::new(module.mod_start as u64, length as u64))
            } else {
                None
            }
        })
    }
}
