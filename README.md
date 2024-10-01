[![crate](https://img.shields.io/crates/v/relp-num.svg)](https://crates.io/crates/relp-num)
[![documentation](https://docs.rs/relp-num/badge.svg)](https://docs.rs/relp-num)
[![build status](https://github.com/vandenheuvel/relp-num/actions/workflows/main.yml/badge.svg?branch=main)](https://github.com/vandenheuvel/relp-num/actions) [![codecov](https://codecov.io/gh/vandenheuvel/relp-num/branch/main/graph/badge.svg)](https://codecov.io/gh/vandenheuvel/relp-num)

# RELP-num
    
Number types for the [Relp](https://github.com/vandenheuvel/relp) crate, most notably arbitrary precision rationals.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
relp-num = "0.1.13"
```

You can now use the crate, for example to compute `2 + 2`:

```rust
fn main() {
    println!("{}", relp_num::RB!(2) + relp_num::R64!(2));
}
```

The first number is represented in arbitrary precision (type [**R**ational**B**ig](https://docs.rs/relp-num/0.1.2/relp_num/type.RationalBig.html)), the second one smaller (type [**R**ational**64**](https://docs.rs/relp-num/0.1.2/relp_num/type.Rational64.html)) with 64 bits of precision for both the numerator and denominator.

## Purpose

The RELP crate computes with rational numbers that have specific properties. They need to be arbitrary precision, but 
are often small. Performance is critical and as such these specific properties should be exploited. This crate does 
exactly that.

Specific linear programs that one wishes to solve with RELP might have specific properties. RELP allows the user to
specialize default implementations in order to exploit these. This numerics crate contains default implementations of
number types for this usecase.

### What this crate is not

There are already some great general purpose numerics libraries out there, such as 

- [num](https://github.com/rust-num/num) (broad range of functionality)
- [ramp](https://github.com/Aatch/ramp) (arbitrary precision, fast, requires nightly)

This crate is not trying to be one of them and exists to support RELP only.
