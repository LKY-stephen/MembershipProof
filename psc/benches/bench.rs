use criterion::{criterion_group, criterion_main, Criterion};

use psc::{Psc, SetCommitment};
use rand::{seq::SliceRandom, Rng};

use std::{collections::HashSet, time::Duration};

const LN: usize = 4;
const LB: usize = 3;

fn proof_criterion_256(c: &mut Criterion) {
    seq_macro::seq!(M in 32..64 {
        generate_proof_fn::<M>(c);
    });
}

fn generate_proof_fn<const M: usize>(c: &mut Criterion) {
    for n in 10..=20 {
        let (set, psc) = prepare_set::<M>(n);
        let element = set.choose(&mut rand::thread_rng()).expect("set is empty");
        let (param, pk) = Psc::<4, 32, 3>::zk_setup();

        // bench setup
        c.bench_function(
            &format!("Setup for prove key and verification key for n:{n} m: {M}"),
            |b| {
                b.iter(|| {
                    Psc::<4, 32, 3>::zk_setup();
                })
            },
        );

        let proof = psc.zk_prove(element, &param, &pk);

        // bench membership proof
        c.bench_function(&format!("membership proof for n:{n} m: {M}"), |b| {
            b.iter(|| {
                psc.zk_prove(element, &param, &pk);
            })
        });

        println!("proof size is {} bytes", proof.len());

        let (set_commitment, k_commitment) = psc.get_commitment();

        let result = Psc::<LN, M, LB>::zk_verify_membership(
            element,
            &proof,
            &set_commitment,
            &k_commitment,
            &param,
            pk.get_vk(),
        );
        assert_eq!(result.is_ok(), true);
        assert_eq!(result.unwrap(), true);

        c.bench_function(&format!("membership verification for n:{n} m: {M}"), |b| {
            b.iter(|| {
                Psc::<LN, M, LB>::zk_verify_membership(
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
        let proof = psc.zk_prove(&fake_element, &param, &pk);

        // bench non-membership proof
        c.bench_function(&format!("non-membership proof for n:{n} m: {M}"), |b| {
            b.iter(|| {
                psc.zk_prove(&fake_element, &param, &pk);
            })
        });

        let (set_commitment, k_commitment) = psc.get_commitment();
        let result = Psc::<LN, M, LB>::zk_verify_membership(
            &fake_element,
            &proof,
            &set_commitment,
            &k_commitment,
            &param,
            pk.get_vk(),
        );
        // bench non-membership proof
        c.bench_function(
            &format!("non-membership verification for n:{n} m: {M}"),
            |b| {
                b.iter(|| {
                    Psc::<LN, M, LB>::zk_verify_membership(
                        &fake_element,
                        &proof,
                        &set_commitment,
                        &k_commitment,
                        &param,
                        pk.get_vk(),
                    )
                    .unwrap();
                })
            },
        );

        assert_eq!(result.is_ok(), true);
        assert_eq!(result.unwrap(), false);
    }
}

fn prepare_set<const M: usize>(n: usize) -> (Vec<[u64; LN]>, Psc<LN, M, LB>) {
    let set_size = 1 << n;
    println!("Generate test set");
    let set = gen_rand_list(set_size).into_iter().collect::<Vec<_>>();

    let psc = Psc::<LN, M, LB>::new(&set);

    println!("Commit scheme completed");
    return (set, psc);
}

fn gen_rand_list(num: usize) -> HashSet<[u64; LN]> {
    let mut rng = rand::thread_rng();
    let mut set = HashSet::with_capacity(num);

    for _ in 0..num {
        set.insert([rng.gen::<u64>(), rng.gen::<u64>(), rng.gen::<u64>(), 1]);
    }

    return set;
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(30)).sample_size(10);
    targets = proof_criterion_256
}
criterion_main!(benches);
