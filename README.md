# RELP-num
    
Number types for the [RELP](https://github.com/vandenheuvel/relp) crate.

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
