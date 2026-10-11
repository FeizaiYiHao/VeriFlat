OUTPUT_FORMAT("elf64-x86-64")
OUTPUT_ARCH(i386:x86-64)
ENTRY(_start)

SECTIONS {
  PROVIDE (__executable_start = SEGMENT_START("text-segment", 0x400000));
  . = SEGMENT_START("text-segment", 0x400000) + SIZEOF_HEADERS;

  __loader_start = .;

  .multiboot_header :
  {
    KEEP(*(.multiboot_header))
    *(.multiboot_header)
  }

  /* Start relocations */

  .dynamic        : { *(.dynamic) }

  .rela.dyn       :
    {
      *(.rela.init)
      *(.rela.text .rela.text.* .rela.gnu.linkonce.t.*)
      *(.rela.fini)
      *(.rela.rodata .rela.rodata.* .rela.gnu.linkonce.r.*)
      *(.rela.data .rela.data.* .rela.gnu.linkonce.d.*)
      *(.rela.tdata .rela.tdata.* .rela.gnu.linkonce.td.*)
      *(.rela.tbss .rela.tbss.* .rela.gnu.linkonce.tb.*)
      *(.rela.ctors)
      *(.rela.dtors)
      *(.rela.got)
      *(.rela.bss .rela.bss.* .rela.gnu.linkonce.b.*)
      *(.rela.ldata .rela.ldata.* .rela.gnu.linkonce.l.*)
      *(.rela.lbss .rela.lbss.* .rela.gnu.linkonce.lb.*)
      *(.rela.lrodata .rela.lrodata.* .rela.gnu.linkonce.lr.*)
      *(.rela.ifunc)
    }
  .rela.plt       :
    {
      *(.rela.plt)
      PROVIDE_HIDDEN (__rela_iplt_start = .);
      *(.rela.iplt)
      PROVIDE_HIDDEN (__rela_iplt_end = .);
    }
  .relr.dyn : { *(.relr.dyn) }

  /* End relocations */

  .rodata :
  {
    *(.rodata .rodata.*)
    . = ALIGN(4K);
  }

  .entry.text :
  {
    __entry_text_start = .;
    KEEP(*(.entry.text))
    *(.entry.text .entry.text.*)
    . = ALIGN(4K);
    __entry_text_end = .;
  }

  .text :
  {
    __text_start = .;
    *(.text .text.*)
    . = ALIGN(4K);
    __text_end = .;
  }

  .rodata :
  {
     __rodata_start = .;
     *(.rodata*)
     . = ALIGN(4096);
     __rodata_end = .;
  }

  .data :
  {
    __data_start = .;
    *(.data .data.*)
    . = ALIGN(4K);
    __data_end = .;
  }

  .bss :
  {
    __bss_start = .;
    *(.bss .bss.*)
    . = ALIGN(4K);
    __bss_end = .;
  }

  .tdata :
  {
    __tdata_start = .;
    *(.tdata*)
    . = ALIGN(4096);
    __tdata_end = .;
    __tbss_start = .;
    *(.tbss*)
    . += 8;
    . = ALIGN(4096);
    __tbss_end = .;
  }

  .got.plt :
  {
    *(.got.plt)
    . = ALIGN(4K);
  }

  .got :
  {
    *(.got)
    . = ALIGN(4K);
  }

  .data.rel.ro : ALIGN(4K) {
    *(.data.rel.ro.local*) *(.data.rel.ro .data.rel.ro.*)
    . = ALIGN(4K);
  }

  .gcc_except_table : ALIGN(4K) {
    *(.gcc_except_table)
    . = ALIGN(4K);
  }

  /* `INFO` makes the section not allocatable so it won't be loaded into memory */
  .stack_sizes (INFO) :
  {
    KEEP(*(.stack_sizes));
  }

  . = ALIGN(4K);
  __loader_end = .;
}
