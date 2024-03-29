#[cfg(test)]
mod tests {
    use psc::traits::*;
    use psc::Psc;
    use rand::seq::SliceRandom;
    use rand::{self, Rng};
    use rstest::rstest;
    use std::collections::HashSet;

    #[rstest]
    #[case(100)]
    #[case(1000)]
    #[case(10_000)]
    fn random_plain_proof_tests(#[case] num: usize) {
        println!("Generate test set");
        let set = gen_rand_list(num).into_iter().collect::<Vec<_>>();
        println!("Generate PSC dict");
        let psc = Psc::<4, 32, 3>::new(&set);
        println!("Start Querying");

        let element = set.choose(&mut rand::thread_rng()).expect("set is empty");
        let witness = psc.prove(element);
        let (set_commitment, k) = psc.get_commitment();
        let result = Psc::<4, 32, 3>::verify_membership(element, &witness, &set_commitment, k);
        assert_eq!(result.is_ok(), true);
        assert_eq!(result.unwrap(), true);

        let fake_element = [1, 1, 1, 0];
        let witness = psc.prove(&fake_element);

        let result =
            Psc::<4, 32, 3>::verify_membership(&fake_element, &witness, &set_commitment, k);
        assert_eq!(result.is_ok(), true);
        assert_eq!(result.unwrap(), false);
    }

    #[rstest]
    #[case(100)]
    #[case(1000)]
    #[case(10_000)]
    fn random_eh_halo_tests(#[case] num: usize) {
        const LN: usize = 4;
        const LE: usize = 3;
        const M: usize = 32;

        println!("Generate test set");
        let set = gen_rand_list(num).into_iter().collect::<Vec<_>>();
        println!("Generate PSC dict");
        let psc = Psc::<LN, M, LE>::new(&set);
        println!("Start Querying");

        let element = set.choose(&mut rand::thread_rng()).expect("set is empty");
        let (param, pk) = Psc::<LN, M, LE>::eh_setup();
        let proof = psc.eh_prove_halo(element, &param, &pk);
        let (set_commitment, k) = psc.get_commitment();
        let result =
            Psc::<LN, M, LE>::eh_verify_halo(&proof, &set_commitment, k, &param, pk.get_vk());
        assert_eq!(result.is_ok(), true);
        assert_eq!(result.unwrap(), true);

        let fake_element = [1, 1, 1, 0];
        let proof = psc.eh_prove_halo(&fake_element, &param, &pk);
        let result =
            Psc::<LN, M, LE>::eh_verify_halo(&proof, &set_commitment, k, &param, pk.get_vk());
        assert_eq!(result.is_ok(), true);
        assert_eq!(result.unwrap(), false);
    }

    fn gen_rand_list(num: usize) -> HashSet<[u64; 4]> {
        let mut rng = rand::thread_rng();
        let mut set = HashSet::with_capacity(num);

        for _ in 0..num {
            set.insert([rng.gen::<u64>(), rng.gen::<u64>(), rng.gen::<u64>(), 1]);
        }

        return set;
    }
}
