use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, BenchmarkId, Criterion,
};

use psc::{Psc, SetCommitment};
use rand::{seq::SliceRandom, Rng};

use std::{collections::HashSet, time::Duration};

const LN: usize = 4;
const LB: usize = 3;

fn bench_with_m(c: &mut Criterion) {
    let set = gen_rand_list(10);
    let mut group = c.benchmark_group("with_changed_m");
    seq_macro::seq!(M in 32..64 {
        bench_halo::<M,_>(&set, &mut group,|s: &str| BenchmarkId::new(&format!("{s} for n: 10 ", ), M));
    });

    group.finish();
}

fn bench_with_n(c: &mut Criterion) {
    let mut group = c.benchmark_group("with_changed_n");
    for n in 5..=20 {
        let set = gen_rand_list(n);
        bench_halo::<32, _>(&set, &mut group, |s: &str| {
            BenchmarkId::new(&format!("{s} for m: 32 ",), n)
        });
    }

    group.finish();
}

fn bench_halo<const M: usize, F: Fn(&str) -> BenchmarkId>(
    set: &Vec<[u64; LN]>,
    group: &mut BenchmarkGroup<WallTime>,
    gen_id: F,
) {
    let psc = Psc::<LN, M, LB>::new(&set);
    let element = set.choose(&mut rand::thread_rng()).expect("set is empty");
    let (param, pk) = Psc::<LN, M, LB>::zk_setup();

    // bench setup
    group.bench_function(gen_id("set up"), |b| {
        b.iter(|| {
            Psc::<LN, M, LB>::zk_setup();
        })
    });

    let proof = psc.zk_prove_halo(element, &param, &pk);

    // bench membership proof
    group.bench_function(gen_id("membership proof"), |b| {
        b.iter(|| {
            psc.zk_prove_halo(element, &param, &pk);
        })
    });

    println!("proof size is {} bytes", proof.len());

    let (set_commitment, k_commitment) = psc.get_commitment();

    let result = Psc::<LN, M, LB>::zk_verify_halo(
        element,
        &proof,
        &set_commitment,
        &k_commitment,
        &param,
        pk.get_vk(),
    );
    assert_eq!(result.is_ok(), true);
    assert_eq!(result.unwrap(), true);

    group.bench_function(gen_id("membership verification"), |b| {
        b.iter(|| {
            Psc::<LN, M, LB>::zk_verify_halo(
                element,
                &proof,
                &set_commitment,
                &k_commitment,
                &param,
                pk.get_vk(),
            )
            .unwrap();
        })
    });

    let fake_element = [1, 1, 1, 0];
    let proof = psc.zk_prove_halo(&fake_element, &param, &pk);

    // bench non-membership proof
    group.bench_function(gen_id("non-membership proof"), |b| {
        b.iter(|| {
            psc.zk_prove_halo(&fake_element, &param, &pk);
        })
    });

    let (set_commitment, k_commitment) = psc.get_commitment();
    let result = Psc::<LN, M, LB>::zk_verify_halo(
        &fake_element,
        &proof,
        &set_commitment,
        &k_commitment,
        &param,
        pk.get_vk(),
    );
    // bench non-membership proof
    group.bench_function(gen_id("non-membership verification"), |b| {
        b.iter(|| {
            Psc::<LN, M, LB>::zk_verify_halo(
                &fake_element,
                &proof,
                &set_commitment,
                &k_commitment,
                &param,
                pk.get_vk(),
            )
            .unwrap();
        })
    });

    assert_eq!(result.is_ok(), true);
    assert_eq!(result.unwrap(), false);
}

fn gen_rand_list(n: usize) -> Vec<[u64; LN]> {
    let set_size = 1 << n;
    println!("Generate test set");
    let mut rng = rand::thread_rng();
    let mut set = HashSet::with_capacity(set_size);

    let mut filled = 0;
    while filled < set_size {
        if set.insert([rng.gen::<u64>(), rng.gen::<u64>(), rng.gen::<u64>(), 1]) {
            filled += 1;
        }
    }

    return set.into_iter().collect::<Vec<_>>();
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(50)).sample_size(10);
    targets = bench_with_m, bench_with_n
}
criterion_main!(benches);
