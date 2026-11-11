; Multiboot 2 - Compliant Header
; from https://kernelstack.net/2019-07-13-rust-os-1/
; GRUB looks for the header only at 8-byte aligned offsets within the first 32 KiB of the file.
section .multiboot_header align=8
header_start:
    dd 0xe85250d6                ; Magic number identifying this as a header
    dd 0                         ; Specify the CPU as amd64 (32 bit)
    dd header_end - header_start ; Size of the Header
    ; Checksum - Must have value of uint32(0) when added to the value of the other magic fields.
    dd 0x100000000 - (0xe85250d6 + 0 + (header_end - header_start))

    ; Other Multiboot tags will go here.

    ; Required end tag
    dw 0    ; type
    dw 0    ; flags
    dd 8    ; size
header_end:
