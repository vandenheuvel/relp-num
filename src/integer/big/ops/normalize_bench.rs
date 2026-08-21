//! Temporary micro benchmarks; not part of the crate.
use std::hint::black_box;
use std::time::Instant;

use smallvec::SmallVec;

use crate::integer::big::ops::normalize::{binary_gcd, gcd_single, simplify_fraction_without_info};

type SV = SmallVec<[usize; 8]>;

fn rng() -> impl FnMut() -> usize {
    let mut state = 0x2545f4914f6cdd1d_u64;
    move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state as usize
    }
}

fn odd_of(words: usize, next: &mut impl FnMut() -> usize) -> SV {
    let mut v: SV = (0..words).map(|_| next()).collect();
    v[0] |= 1;
    while let Some(0) = v.last() { v.pop(); }
    v
}

fn time(name: &str, iterations: usize, mut f: impl FnMut()) {
    // warm up
    for _ in 0..(iterations / 4 + 1) { f(); }

    // The machine is shared with whatever else runs on it, so take the fastest round: noise only
    // ever adds time.
    let mut best = f64::MAX;
    for _ in 0..9 {
        let start = Instant::now();
        for _ in 0..iterations { f(); }
        let elapsed = start.elapsed().as_nanos() as f64 / iterations as f64;
        if elapsed < best { best = elapsed; }
    }
    println!("{name:50} {best:>12.1} ns/iter");
}

#[test]
fn bench() {
    let mut next = rng();

    for words in [2_usize, 3, 4, 8] {
        let cases: Vec<(SV, usize)> = (0..64)
            .map(|_| (odd_of(words, &mut next), next() | 1))
            .collect();
        let mut i = 0;
        time(&format!("gcd_single, {words} words"), 20_000, || {
            let (large, small) = &cases[i % cases.len()];
            i += 1;
            black_box(unsafe { gcd_single(large, *small, 0) });
        });
    }

    for words in [1_usize, 2, 3, 4, 8] {
        let cases: Vec<(SV, SV)> = (0..32)
            .map(|_| (odd_of(words, &mut next), odd_of(words, &mut next)))
            .collect();
        let mut i = 0;
        let iterations = if words > 4 { 2_000 } else { 20_000 };
        time(&format!("binary_gcd, {words} words"), iterations, || {
            let (left, right) = &cases[i % cases.len()];
            i += 1;
            black_box(unsafe { binary_gcd::<8>(left.clone(), right.clone()) });
        });
    }

    for words in [2_usize, 4] {
        let cases: Vec<(SV, SV)> = (0..32)
            .map(|_| {
                let mut a: SV = (0..words).map(|_| next()).collect();
                let mut b: SV = (0..words).map(|_| next()).collect();
                a[0] |= 1; b[0] |= 1;
                (a, b)
            })
            .collect();
        let mut i = 0;
        time(&format!("simplify_fraction_without_info, {words} words"), 20_000, || {
            let (a, b) = &cases[i % cases.len()];
            let (mut a, mut b) = (a.clone(), b.clone());
            i += 1;
            unsafe { simplify_fraction_without_info(&mut a, &mut b) };
            black_box((a, b));
        });
    }
}
