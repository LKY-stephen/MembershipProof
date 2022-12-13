#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rand::{self, Rng};
    use rstest::rstest;

    #[rstest]
    #[case(10, 5000)]
    #[case(100, 5000)]
    #[case(200, 5000)]
    #[case(500, 5000)]
    #[case(100, 100000)]
    #[case(1000, 100000)]
    #[case(10000, 100000)]
    fn random_u32_list_tests(#[case] num: u32, #[case] max: u32) {
        for _ in 1..=10 {
            println!("Generate test set");
            let set = gen_rand_list(num, max);
            println!("Generate FKS dict");
            let dict = fks_dict::FKSDict::new(&set, max);
            println!("Start Querying");
            for x in 1..=max {
                assert_eq!(dict.query(x), set.contains(&x));
            }
        }
    }

    #[rstest]
    #[case(10, 500)]
    #[case(100, 500)]
    #[case(10, 1000)]
    #[case(100, 1000)]
    #[case(200, 1000)]
    fn random_u32_list_proof_tests(#[case] num: u32, #[case] max: u32) {
        println!("Generate test set");
        let set = gen_rand_list(num, max);
        println!("Generate FKS dict");
        let dict = fks_dict::FKSDict::new(&set, max);
        println!("Start Querying");
        let refer = vec![num, max];
        for x in 1..=max {
            let commit = dict.commit(&refer);
            let proof = dict.gen_proof(x, &refer);
            assert!(fks_dict::verify_commit_proof(
                x,
                &refer,
                &proof,
                commit,
                set.contains(&x)
            ));
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
}
