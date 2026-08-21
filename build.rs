/// The assembly sources, and the cfg the crate uses to tell whether they were compiled.
///
/// The routines in these files hard code the System V argument registers (`rdi`, `rsi`, `rdx`,
/// `rcx`, which is not what Windows passes arguments in), an eight byte limb stride (which assumes
/// a 64 bit `usize`) and ELF assembler directives such as `.section ...,"ax",@progbits`, `.type`
/// and `.size` (which Mach-O does not accept). They are therefore compiled only for 64 bit x86 ELF
/// targets, and only when the default `asm` feature is on; every routine also has a portable Rust
/// implementation that is used everywhere else.
fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    // Declare the cfg even when it is not set, so that `#[cfg(ramp_asm)]` is not reported as an
    // unexpected condition.
    println!("cargo::rustc-check-cfg=cfg(ramp_asm)");

    #[cfg(feature = "asm")]
    if asm::wanted_by_target() {
        asm::compile();
        println!("cargo::rustc-cfg=ramp_asm");
    }
}

/// Only compiled with the `asm` feature, because that is what pulls in the `cc` build dependency;
/// without it the crate needs no C toolchain at all.
#[cfg(feature = "asm")]
mod asm {
    use std::env;

    const SOURCES: &[&str] = &[
        "src/integer/big/ops/asm/addsub_n.S",
        "src/integer/big/ops/asm/mul_1.S",
        "src/integer/big/ops/asm/addmul_1.S",
    ];

    /// Whether this target can use the assembly.
    pub fn wanted_by_target() -> bool {
        // An escape hatch that selects the portable implementations without touching the feature
        // graph, which is how they are exercised end to end on a target that does have the
        // assembly.
        println!("cargo::rerun-if-env-changed=RELP_NUM_DISABLE_ASM");
        if env::var_os("RELP_NUM_DISABLE_ASM").is_some_and(|value| value != "0") {
            return false;
        }

        let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
        let os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
        // Guards against `x86_64-unknown-linux-gnux32`, which is a 64 bit x86 target with a 32 bit
        // `usize` and 32 bit pointers.
        let pointer_width = env::var("CARGO_CFG_TARGET_POINTER_WIDTH").unwrap_or_default();

        arch == "x86_64" && os == "linux" && pointer_width == "64"
    }

    /// Assemble the routines and link them in.
    pub fn compile() {
        for source in SOURCES {
            println!("cargo::rerun-if-changed={source}");
        }

        cc::Build::new().files(SOURCES).compile("libasm.a");
    }
}
