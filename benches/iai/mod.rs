use rational_big::add::{large_with_large_other_denominator, small_with_small_other_denominator, small_with_small_same_denominator};

pub mod rational_big;

iai::main!(
    large_with_large_other_denominator,
    small_with_small_same_denominator,
    small_with_small_other_denominator,
);
