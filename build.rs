fn main() {
    let asm_srcs = &[
        "src/rational/big/ops/asm/addsub_n.S",
        "src/rational/big/ops/asm/mul_1.S",
        "src/rational/big/ops/asm/addmul_1.S",
    ];

    cc::Build::new().files(asm_srcs).compile("libasm.a");
}
