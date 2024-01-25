use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, BenchmarkId, Criterion,
};

use psc::traits::*;
use psc::Psc;
use rand::seq::SliceRandom;

use std::time::Duration;

const LB: usize = 3;

fn bench_with_m(c: &mut Criterion) {
    const LN: usize = 4;
    let set = gen_rand_list::<LN>(10);
    let mut group = c.benchmark_group("with_changed_m");

    // bench_halo::<LN, 12, _>(&set, &mut group, |s: &str| {
    //     BenchmarkId::new(&format!("{s} for n: 10 ",), 12)
    // });
    bench_halo::<LN, 16, _>(&set, &mut group, |s: &str| {
        BenchmarkId::new(&format!("{s} for n: 10 ",), 16)
    });
    // bench_halo::<LN, 32, _>(&set, &mut group, |s: &str| {
    //     BenchmarkId::new(&format!("{s} for n: 10 ",), 32)
    // });
    bench_halo::<LN, 64, _>(&set, &mut group, |s: &str| {
        BenchmarkId::new(&format!("{s} for n: 10 ",), 64)
    });
    // bench_halo::<LN, 128, _>(&set, &mut group, |s: &str| {
    //     BenchmarkId::new(&format!("{s} for n: 10 ",), 128)
    // });
    bench_halo::<LN, 256, _>(&set, &mut group, |s: &str| {
        BenchmarkId::new(&format!("{s} for n: 10 ",), 256)
    });
    group.finish();
}

fn bench_with_n(c: &mut Criterion) {
    const LN: usize = 4;
    let mut group = c.benchmark_group("with_changed_n");
    for n in [10, 15, 20] {
        let set = gen_rand_list::<LN>(n);
        bench_halo::<LN, 32, _>(&set, &mut group, |s: &str| {
            BenchmarkId::new(&format!("{s} for m: 32 ",), n)
        });
    }

    group.finish();
}

fn bench_with_le(c: &mut Criterion) {
    let mut group = c.benchmark_group("with_changed_le");
    seq_macro::seq!(LN in 1..5 {
        let set = gen_rand_list::<LN>(10);
        bench_halo::<LN,32,_>(&set, &mut group,|s: &str| BenchmarkId::new(&format!("{s} for m:32, n: 10 ", ), LN));
    });

    group.finish();
}

fn bench_halo<const LN: usize, const M: usize, F: Fn(&str) -> BenchmarkId>(
    set: &Vec<[u64; LN]>,
    group: &mut BenchmarkGroup<WallTime>,
    gen_id: F,
) {
    let psc = Psc::<LN, M, LB>::new(&set);
    let element = set.choose(&mut rand::thread_rng()).expect("set is empty");
    let (set_commitment, k) = psc.get_commitment();
    let set_size = set.len() as u64;
    let fake_element = [set_size; LN];

    // EH scheme
    let (param, pk) = Psc::<LN, M, LB>::eh_setup();
    let proof = psc.eh_prove_halo(element, &param, &pk);

    // bench membership proof
    group.bench_function(gen_id("EH membership proof"), |b| {
        b.iter(|| {
            psc.eh_prove_halo(element, &param, &pk);
        })
    });

    println!("EH membership proof size is {} bytes", proof.len());

    let result = Psc::<LN, M, LB>::eh_verify_halo(&proof, &set_commitment, k, &param, pk.get_vk());
    assert_eq!(result.is_ok(), true);
    assert_eq!(result.unwrap(), true);

    group.bench_function(gen_id("EH membership verification"), |b| {
        b.iter(|| {
            Psc::<LN, M, LB>::eh_verify_halo(&proof, &set_commitment, k, &param, pk.get_vk())
                .unwrap();
        })
    });

    let proof = psc.eh_prove_halo(&fake_element, &param, &pk);

    println!("EH non-membership proof size is {} bytes", proof.len());
    // bench non-membership proof
    group.bench_function(gen_id("EH non-membership proof"), |b| {
        b.iter(|| {
            psc.eh_prove_halo(&fake_element, &param, &pk);
        })
    });

    let result = Psc::<LN, M, LB>::eh_verify_halo(&proof, &set_commitment, k, &param, pk.get_vk());
    // bench non-membership proof
    group.bench_function(gen_id("EH non-membership verification"), |b| {
        b.iter(|| {
            Psc::<LN, M, LB>::eh_verify_halo(&proof, &set_commitment, k, &param, pk.get_vk())
                .unwrap();
        })
    });

    assert_eq!(result.is_ok(), true);
    assert_eq!(result.unwrap(), false);
}

fn gen_rand_list<const LN: usize>(n: usize) -> Vec<[u64; LN]> {
    let set_size = 1 << n;
    (0..set_size).map(|e| [e; LN]).collect::<Vec<_>>()
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(30)).sample_size(100);
    targets = bench_with_m, bench_with_n, bench_with_le
}
criterion_main!(benches);
