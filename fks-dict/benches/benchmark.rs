use std::collections::HashSet;

use criterion::{criterion_group, criterion_main, Criterion};
use rand::{self, Rng};

pub fn criterion_build_dict(c: &mut Criterion) {
    for num in [100, 1000, 10000] {
        let inputs = gen_rand_list(num, num * 10);
        c.bench_function(&format!("Build dict {}", num), |b| {
            b.iter(|| fks_dict::FKSDict::new(&inputs, num * 10))
        });
    }
}

pub fn criterion_commit(c: &mut Criterion) {
    let reference = vec![114514u32, 71263u32];
    for num in [100, 1000, 10000] {
        let inputs = gen_rand_list(num, num * 10);
        let dict = fks_dict::FKSDict::new(&inputs, num * 10);
        c.bench_function(&format!("Commit dict {}", num), |b| {
            b.iter(|| dict.commit(&reference))
        });
    }
}

pub fn criterion_prove_exist(c: &mut Criterion) {
    let reference = vec![114514u32, 71263u32];
    for num in [100, 1000, 10000] {
        let inputs = gen_rand_list(num, num * 10);
        let ele = *inputs.iter().next().unwrap();
        let dict = fks_dict::FKSDict::new(&inputs, num * 10);
        c.bench_function(&format!("prove exists {}", num), |b| {
            b.iter(|| dict.gen_proof(ele, &reference));
        });
    }
}

pub fn criterion_prove_non_exist(c: &mut Criterion) {
    let reference = vec![114514u32, 71263u32];
    let mut rng = rand::thread_rng();
    for num in [100, 1000, 10000] {
        let ele = rng.gen_range(num * 10..num * 100);
        let inputs = gen_rand_list(num, num * 10);
        let dict = fks_dict::FKSDict::new(&inputs, num * 10);
        c.bench_function(&format!("prove non exists {}", num), |b| {
            b.iter(|| dict.gen_proof(ele, &reference));
        });
    }
}

pub fn criterion_verify_non_exist(c: &mut Criterion) {
    let reference = vec![114514u32, 71263u32];
    let mut rng = rand::thread_rng();
    for num in [100, 1000, 10000] {
        let ele = rng.gen_range(num * 10..num * 100);
        let inputs = gen_rand_list(num, num * 10);
        let dict = fks_dict::FKSDict::new(&inputs, num * 10);
        let prove = dict.gen_proof(ele, &reference);
        let commit = dict.commit(&reference);
        c.bench_function(&format!("verify non exists {}", num), |b| {
            b.iter(|| fks_dict::verify_commit_proof(ele, &reference, &prove, &commit, false));
        });
    }
}

pub fn criterion_verify_exist(c: &mut Criterion) {
    let reference = vec![114514u32, 71263u32];
    for num in [100, 1000, 10000] {
        let inputs = gen_rand_list(num, num * 10);
        let ele = *inputs.iter().next().unwrap();
        let dict = fks_dict::FKSDict::new(&inputs, num * 10);
        let prove = dict.gen_proof(ele, &reference);
        let commit = dict.commit(&reference);
        c.bench_function(&format!("verify exists {}", num), |b| {
            b.iter(|| fks_dict::verify_commit_proof(ele, &reference, &prove, &commit, true));
        });
    }
}

fn gen_rand_list(num: u32, max: u32) -> HashSet<u32> {
    let mut rng = rand::thread_rng();
    let mut set: HashSet<u32> = HashSet::new();

    while set.len() < num as usize {
        set.insert(rng.gen_range(1..max));
    }

    return set;
}
criterion_group!(
    benches,
    criterion_build_dict,
    criterion_commit,
    criterion_prove_exist,
    criterion_prove_non_exist,
    criterion_verify_exist,
    criterion_verify_non_exist
);
criterion_main!(benches);
