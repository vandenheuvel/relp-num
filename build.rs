fn main() {
    let asm_srcs = &[
        "src/integer/big/ops/asm/addsub_n.S",
        "src/integer/big/ops/asm/mul_1.S",
        "src/integer/big/ops/asm/addmul_1.S",
    ];

    cc::Build::new().files(asm_srcs).compile("libasm.a");
}
