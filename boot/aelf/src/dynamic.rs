//! Relocation fixups.

use core::mem;
use core::ptr;
use core::slice;

use super::{
    elf_types,
    elf_types::dynamic::{DT_NULL, DT_REL, DT_RELA, DT_RELAENT, DT_RELASZ, DT_RELENT, DT_RELSZ},
    elf_types::program_header::{ProgramHeader, PT_DYNAMIC},
    R_RELATIVE,
};

pub struct Dynamic {
    ptr: *const elf_types::dynamic::Dyn,
    load_bias: usize,
    load_bias_loader: usize,
}

impl Dynamic {
    pub fn from_program_headers<'a>(
        mut phs: impl Iterator<Item = &'a ProgramHeader>,
        load_bias: usize,
        load_bias_loader: usize,
    ) -> Option<Self> {
        phs.find(|ph| ph.p_type == PT_DYNAMIC).map(|ph| {
            let ptr = load_bias_loader.wrapping_add(ph.p_vaddr as usize)
                as *const elf_types::dynamic::Dyn;
            Self {
                ptr,
                load_bias,
                load_bias_loader,
            }
        })
    }

    pub fn fixup(self) {
        let mut cur = self.ptr;

        let mut rela_data = None;
        let mut rela_len = None;

        let mut rel_data = None;
        let mut rel_len = None;

        loop {
            let entry = unsafe { &*cur };

            #[allow(clippy::unnecessary_cast)] // it's necessary with ELF32
            match entry.d_tag as u64 {
                DT_NULL => break,

                // DT_RELA
                DT_RELA => {
                    rela_data = Some(entry.d_val.wrapping_add(self.load_bias_loader as _)
                        as *const elf_types::reloc::Rela);
                }
                DT_RELASZ => {
                    rela_len =
                        Some(entry.d_val as usize / mem::size_of::<elf_types::reloc::Rela>());
                }
                DT_RELAENT => {
                    let actual_size = entry.d_val as usize;
                    if actual_size != mem::size_of::<elf_types::reloc::Rela>() {
                        panic!("DT_RELAENT has unsupported size");
                    }
                }

                // DT_REL
                DT_REL => {
                    rel_data = Some(entry.d_val.wrapping_add(self.load_bias_loader as _)
                        as *const elf_types::reloc::Rel);
                }
                DT_RELSZ => {
                    rel_len = Some(entry.d_val as usize / mem::size_of::<elf_types::reloc::Rel>());
                }
                DT_RELENT => {
                    let actual_size = entry.d_val as usize;
                    if actual_size != mem::size_of::<elf_types::reloc::Rel>() {
                        panic!("DT_RELENT has unsupported size");
                    }
                }

                _ => {}
            }

            cur = unsafe { cur.add(1) };
        }

        if let (Some(rela_data), Some(rela_len)) = (rela_data, rela_len) {
            let rela = unsafe { slice::from_raw_parts(rela_data, rela_len) };
            for reloc in rela {
                let r_type = elf_types::reloc::r_type(reloc.r_info);
                if r_type != R_RELATIVE {
                    panic!("Unsupported relocation type");
                }

                let relocated = self.load_bias.wrapping_add(reloc.r_addend as usize);
                let ptr = self.load_bias_loader.wrapping_add(reloc.r_offset as usize) as *mut usize;
                // log::debug!("RELA ptr={:?}, offset=0x{:x}, addend=0x{:x}, actual=0x{:x}", ptr, reloc.r_offset, reloc.r_addend, relocated);

                unsafe {
                    ptr::write_unaligned(ptr, relocated);
                }
            }
        }

        if let (Some(rel_data), Some(rel_len)) = (rel_data, rel_len) {
            let rel = unsafe { slice::from_raw_parts(rel_data, rel_len) };
            for reloc in rel {
                let r_type = elf_types::reloc::r_type(reloc.r_info);
                if r_type != R_RELATIVE {
                    panic!("Unsupported relocation type");
                }

                let ptr = self.load_bias_loader.wrapping_add(reloc.r_offset as usize) as *mut usize;
                unsafe {
                    let addend = *ptr;
                    let relocated = self.load_bias.wrapping_add(addend);
                    *ptr = relocated;
                }
            }
        }
    }
}
