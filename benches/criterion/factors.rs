use criterion::{black_box, Criterion, criterion_group};

use relp_num::NonZeroFactorizable;

fn factor_small(c: &mut Criterion) {
    c.bench_function("factorize a small number", |b| b.iter(|| {
        NonZeroFactorizable::factorize(black_box(&31_u64))
    }));
}

criterion_group!(group,
    factor_small,
);
