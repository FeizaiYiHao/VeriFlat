#![deny(unused_must_use)]

macro_rules! source {
    ($($arg:tt)*) => {
        println!("cargo:rerun-if-changed={}", format_args!($($arg)*));
    };
}

fn main() {
    source!("build.rs");
    source!("src/linker.ld");
    add_x86_64_asm("multiboot2_header.asm");
    add_x86_64_asm("crt0.asm");

    // The loader is linked at a fixed physical address by its own linker
    // script and never relocates itself, so override the static-pie default
    // of x86_64-unknown-none with a plain static link.
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    println!("cargo:rustc-link-arg-bins=--no-pie");
    println!("cargo:rustc-link-arg-bins=-T{}/src/linker.ld", manifest_dir);
}

/// Adds code from a NASM assembly file to the image.
fn add_x86_64_asm(source: &str) {
    let arch_dir = "src/boot";
    source!("{}/{}", arch_dir, source);

    let mut mb = nasm_rs::Build::new();
    mb.file(&format!("{}/{}", arch_dir, source));
    mb.target("");
    mb.flag("-felf64");

    let objects = mb.compile_objects().unwrap();
    for object in objects {
        println!("cargo:rustc-link-arg-bins={}", object.to_str().unwrap());
    }
}
