mod buckets;
mod halo_circuit;
mod hashes;
mod poseidon_spec;
mod proof;
pub mod traits;

use crate::buckets::Buckets;
use crate::buckets::Node;
use crate::halo_circuit::eh_circuit::MerkleExtendedPathEHCircuit;
use crate::hashes::*;
use crate::poseidon_spec::PoseidonSpec;
use ff::Field;
use ff::PrimeField;
use halo2_proofs::circuit::Value;
use halo2_proofs::pasta::{EqAffine, Fp};
use halo2_proofs::plonk::{
    create_proof, keygen_pk, keygen_vk, verify_proof, ProvingKey, SingleVerifier, VerifyingKey,
};
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use proof::EHProof;
use proof::Proof;
use rand::rngs::OsRng;
use traits::EHScheme;
use traits::SetCommitment;

/// Psc is an auxirary for a set of elements and supports to generate
/// prove that a given element is in or not in the set.
/// F is the field to be used in ZKP
/// LE is the length of the element per 8 bytes
/// LM is the log size of the maximum set
/// LB is the log size of the backet
pub struct Psc<const LE: usize, const LM: usize, const LB: usize> {
    aux: Vec<Vec<Node>>,
    set_commitment: [u8; 32],
    k: u32,
    rk: u64,
}

impl<const LE: usize, const LM: usize, const LB: usize> Psc<LE, LM, LB> {
    const BUCKET_SIZE: usize = 1 << LB as u32;

    pub fn new(set: &Vec<[u64; LE]>) -> Self {
        if (set.len() as f64).log2().round() as usize + 1 > LM {
            panic!("The size of the set is too large");
        }

        let rk = rand::random::<u64>();
        let keys: Vec<[u64; LE]> = set
            .into_iter()
            .map(|x| x.to_owned().map(|v| v.wrapping_add(rk)))
            .collect();

        // initate the vec k.
        let mut buckets = Buckets::new(keys);

        #[cfg(debug_assertions)]
        println!("Start spliting");
        buckets.split(set.len(), Self::BUCKET_SIZE);

        // fill the rest of k with 0
        // technically, here we should use a more random value here
        // for simiplicity, we just add one per step.

        let k = buckets.get_k();

        #[cfg(debug_assertions)]
        println!("bucket k is {k}");
        // commit the set

        // initialize the leave array and covert each leaf to a Fp node;

        #[cfg(debug_assertions)]
        println!("Start maping for buckets");
        let mut aux = vec![buckets.init_aux(Self::BUCKET_SIZE, rk)];
        let raw_leaves = aux.first().expect("empty leaves");
        aux.push(raw_leaves.iter().map(poseidonhash_node::<LE>).collect());

        // recursively compute the root.
        while aux.last().unwrap().len() > 1 {
            let hashes = aux.last().unwrap();
            let mut next_hashes = Vec::new();
            for chunk in hashes.chunks(2) {
                let hash = match chunk.len() == 2 {
                    true => poseidon_merkle_hash(&chunk[0], &chunk[1]),
                    false => poseidon_merkle_hash(&chunk[0], &chunk[0]),
                };
                next_hashes.push(hash);
            }
            aux.push(next_hashes);
        }

        // get the root
        #[cfg(debug_assertions)]
        println!("compute the commitment");

        if let Node::Field(root) = aux.last().unwrap()[0] {
            let set_commitment = root.to_repr();

            Self {
                aux,
                set_commitment,
                k,
                rk,
            }
        } else {
            panic!("root is not a field element");
        }
    }

    pub fn get_commitment(&self) -> ([u8; 32], u32) {
        (self.set_commitment.clone(), self.k)
    }

    fn get_position_r(&self, element: &[u64; LE]) -> (usize, u32) {
        // n is depth of real tree
        let n = self.get_n();
        let bucket_position = get_top_bits(self.k, element, n) << LB;

        // fetch the first leaf of the bucket
        let bucket_leaf = &self.aux[0][bucket_position];
        let r = match bucket_leaf {
            Node::Field(_) => panic!("raw leaf should not be a filed"),
            Node::Raw((_, r, _)) => r.to_owned(),
        };
        // fetch the real leaf
        let position = bucket_position + get_bucket_index(element, self.rk, r, Self::BUCKET_SIZE);

        return (position, r);
    }

    fn get_merkle_path(&self, mut position: usize) -> (Vec<Node>, Vec<Node>) {
        let n = self.get_n() + LB;

        let mut left = vec![];
        let mut right = vec![];
        for level in 0..n {
            if position % 2 == 0 {
                left.push(self.aux[level + 1][position].clone());
                right.push(self.aux[level + 1][position + 1].clone());
            } else {
                right.push(self.aux[level + 1][position].clone());
                left.push(self.aux[level + 1][position - 1].clone());
            }
            position /= 2;
        }

        (left, right)
    }

    fn get_n(&self) -> usize {
        self.aux.len() - 2 - LB
    }

    fn get_copy(&self) -> Vec<Value<Fp>> {
        // Bucket will ignore copy so we start with one,
        let mut copy = vec![Value::known(Fp::ONE); LM - self.get_n() - 1];
        // Final part no copy
        copy.resize_with(LM, || Value::known(Fp::ZERO));
        copy
    }
}

impl<const LE: usize, const LM: usize, const LB: usize> SetCommitment<LE, LM, LB>
    for Psc<LE, LM, LB>
{
    type Element = [u64; LE];

    fn prove(&self, element: &Self::Element) -> Proof<LE, LB> {
        // fetch the path

        let shift = element.to_owned().map(|x| x.wrapping_add(self.rk));

        let (position, r) = self.get_position_r(&shift);

        let (left, right) = self.get_merkle_path(position);

        Proof::new(self.rk, r, left, right)
    }

    fn verify_membership(
        element: &Self::Element,
        proof: &Proof<LE, LB>,
        set_commitment: &[u8; 32],
        k: u32,
    ) -> Result<bool, String> {
        // verify the k commitment
        Ok(proof.verify(element, set_commitment, k)?)
    }
}

impl<const LE: usize, const LM: usize, const LB: usize> EHScheme<LE, LM, LB> for Psc<LE, LM, LB> {
    type Element = [u64; LE];
    fn eh_prove_halo(
        &self,
        element: &Self::Element,
        param: &Params<EqAffine>,
        pk: &ProvingKey<EqAffine>,
    ) -> EHProof<LE, LM, LB> {
        const W: usize = 3;
        const R: usize = W - 1;

        // n is depth of real tree
        let shifted = element.to_owned().map(|x| x.wrapping_add(self.rk));
        let (position, r) = self.get_position_r(&shifted);

        let leaf = self.aux[1][position].clone();
        let leaf_value = match &self.aux[0][position] {
            Node::Field(_) => panic!("raw leaf should not be a filed"),
            Node::Raw((rk_read, r_read, v)) => {
                assert_eq!(self.rk, *rk_read);
                assert_eq!(r, *r_read);
                let mut value = v.to_owned();
                value.resize(4, 0);
                Value::known(Fp::from_raw(value.try_into().unwrap()))
            }
        };

        let mut proof = EHProof::new(
            get_split_hash(self.k, &shifted),
            get_bucket_hash(self.rk, r, &shifted),
            match leaf {
                Node::Field(f) => f,
                Node::Raw(_) => panic!("leaf should be a filed element"),
            },
        );

        let (left, right) = self.get_merkle_path(position);

        // create the value for queried element
        let mut value = shifted.to_vec();
        value.resize(4, 0);
        let target = Value::known(Fp::from_raw(value.try_into().unwrap()));

        // create the circuit
        let prover_circuit =
            MerkleExtendedPathEHCircuit::<Fp, PoseidonSpec<W, R>, LM, W, R, LB>::new(
                vec![target],
                vec![leaf_value],
                vec![Value::known(Fp::from(self.rk as u64))],
                vec![Value::known(Fp::from(r as u64))],
                left.into_iter()
                    .map(|x| match x {
                        Node::Field(f) => vec![Value::known(f)],
                        _ => panic!("left should be a field element"),
                    })
                    .collect(),
                right
                    .into_iter()
                    .map(|x| match x {
                        Node::Field(f) => vec![Value::known(f)],
                        _ => panic!("left should be a field element"),
                    })
                    .collect(),
                self.get_copy(),
            );

        // fill in the full path

        let public = proof.create_instance(&self.set_commitment, self.k);

        // [r, r_hashed, k, k_hashed, leaf, index, root]

        #[cfg(debug_assertions)]
        {
            use halo2_proofs::dev::MockProver;
            // over kill k just for test purpose
            let prover = MockProver::run(20, &prover_circuit, vec![public.clone()]).unwrap();
            // Generate the DOT graph string.
            // let dot_string = halo2_proofs::dev::circuit_dot_graph(&prover_circuit);

            // Now you can either handle it in Rust, or just
            // print it out to use with command-line tools.
            // print!("{}", dot_string);
            prover.assert_satisfied();
        }

        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        // Create a proof
        create_proof(
            param,
            pk,
            &[prover_circuit],
            &[&[&public]],
            OsRng,
            &mut transcript,
        )
        .expect("proof generation failed");
        proof.update_proof(transcript.finalize());
        proof
    }

    fn eh_verify_halo(
        proof: &EHProof<LE, LM, LB>,
        set_commitment: &[u8; 32],
        k: u32,
        param: &Params<EqAffine>,
        vk: &VerifyingKey<EqAffine>,
    ) -> Result<bool, String> {
        // verify the k commitment

        let public = proof.create_instance(set_commitment, k);

        let membership = proof.get_membership();
        // compute bucket index

        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof.proof());
        let strategy = SingleVerifier::new(param);
        // verify the path
        let result = verify_proof(param, vk, strategy, &[&[&public]], &mut transcript);

        match result {
            Ok(_) => Ok(membership),
            Err(error) => panic!("Problem opening the file: {:?}", error),
        }
    }

    fn eh_setup() -> (Params<EqAffine>, ProvingKey<EqAffine>) {
        const POSEIDON_DEGREE: u32 = 7;
        const W: usize = 3;
        const R: usize = W - 1;

        let empty_circuit =
            MerkleExtendedPathEHCircuit::<Fp, PoseidonSpec<W, R>, LM, W, R, LB>::new(
                vec![Value::unknown()],
                vec![Value::unknown()],
                vec![Value::unknown()],
                vec![Value::unknown()],
                vec![vec![Value::unknown(); 1]; LM],
                vec![vec![Value::unknown(); 1]; LM],
                vec![Value::unknown(); LM],
            );

        // search for the best k
        let mut k = POSEIDON_DEGREE;
        let (param, vk) = loop {
            let param = Params::new(k);
            let result = keygen_vk(&param, &empty_circuit);
            if result.is_ok() {
                break (param, result.unwrap());
            }
            k += 1;
        };
        #[cfg(debug_assertions)]
        println!("proof k is {k}");

        let pk = keygen_pk(&param, vk, &empty_circuit).expect("keygen_pk should not fail");
        return (param, pk);
    }
}
