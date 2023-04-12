mod buckets;
mod halo_circuit;
mod hashes;
mod poseidon_spec;
mod proof;
pub mod traits;

use crate::buckets::Buckets;
use crate::buckets::Node;
use crate::halo_circuit::eh_circuit::MerkleExtendedPathEHCircuit;
use crate::halo_circuit::sh_circuit::MerkleExtendedPathSHCircuit;
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
use proof::SHProof;
use rand::rngs::OsRng;
use traits::EHScheme;
use traits::SHScheme;
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
    k_commitment: [u64; 4],
    k: Vec<u32>,
}

impl<const LE: usize, const LM: usize, const LB: usize> Psc<LE, LM, LB> {
    const BUCKET_SIZE: usize = 1 << LB as u32;
    const MAX_TREE_DEPTH: usize = LM - LB;

    pub fn new(set: &Vec<[u64; LE]>) -> Self {
        if (set.len() as f64).log2().round() as usize + 1 > LM {
            panic!("The size of the set is too large");
        }

        let keys: Vec<[u64; LE]> = set
            .into_iter()
            .map(|x| {
                x.to_owned()
                    .try_into()
                    .expect("slice with incorrect length")
            })
            .collect();

        // initate the vec k.
        let mut buckets = Buckets::new(keys);

        // println!("Start spliting");
        buckets.split(set.len(), Self::BUCKET_SIZE);

        // fill the rest of k with 0
        // technically, here we should use a more random value here
        // for simiplicity, we just add one per step.

        let mut k = buckets.get_k();
        let mut last = k.last().expect("empty k").to_owned();
        k.resize_with(Self::MAX_TREE_DEPTH, || {
            last += 1;
            last
        });

        // compute k_commitment by hashing k
        let k_commitment = highwayhash_default_256(&k);

        // commit the set

        // initialize the leave array and covert each leaf to a Fp node;

        // println!("Start maping for buckets");
        let mut aux = vec![buckets.init_aux(Self::BUCKET_SIZE)];
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
        // println!("Start commiting for buckets");
        if let Node::Field(root) = aux.last().unwrap()[0] {
            let set_commitment = root.to_repr();

            Self {
                aux,
                set_commitment,
                k_commitment,
                k: k.try_into().expect("vec with incorrect length"),
            }
        } else {
            panic!("root is not a field element");
        }
    }

    pub fn get_commitment(&self) -> ([u8; 32], [u64; 4]) {
        (self.set_commitment.clone(), self.k_commitment.clone())
    }

    fn get_position_r(&self, element: &[u64; LE]) -> (usize, u32) {
        let index = self
            .k
            .iter()
            .map(|k| (get_k_index(*k, &element) & 1) as usize)
            .collect::<Vec<_>>();

        assert_eq!(index.len(), Self::MAX_TREE_DEPTH);

        // n is depth of real tree
        let n = self.aux.len() - 2;

        let mut position = index.iter().take(n - LB).fold(0, |acc, &x| (acc << 1) + x) << LB;

        // fetch the first leaf of the bucket
        let bucket_leaf = &self.aux[0][position];
        let r = match bucket_leaf {
            Node::Field(_) => panic!("raw leaf should not be a filed"),
            Node::Raw((r, _)) => r.to_owned(),
        };
        // fetch the real leaf
        position += get_bucket_index(element, r, Self::BUCKET_SIZE as usize - 1);

        return (position, r);
    }

    fn get_merkle_path(&self, mut position: usize) -> (Vec<Node>, Vec<Node>) {
        let n = self.aux.len() - 2;

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
        self.aux.len() - 2
    }

    fn get_copy(&self) -> Vec<Value<Fp>> {
        let mut copy = vec![Value::known(Fp::ONE); LM - self.get_n() + LB - 1];
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
        let (position, r) = self.get_position_r(element);

        let (left, right) = self.get_merkle_path(position);

        Proof::new(r, self.k.clone(), left, right)
    }

    fn verify_membership(
        element: &Self::Element,
        proof: &Proof<LE, LB>,
        set_commitment: &[u8; 32],
        k_commitment: &[u64; 4],
    ) -> Result<bool, String> {
        // verify the k commitment
        proof.verify_k(k_commitment)?;

        Ok(proof.verify(element, set_commitment)?)
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

        let (position, r) = self.get_position_r(element);

        let leaf = self.aux[1][position].clone();

        let mut hashed = vec![];

        for i in 0..(LM - LB) {
            let k = self.k[i];
            let v = get_keyed_hash(k, element);
            hashed.push(v);
        }

        let bucket_hash = get_keyed_hash(r, element);
        hashed.push(bucket_hash);

        let mut proof = EHProof::new(
            r,
            self.k.clone(),
            match leaf {
                Node::Field(f) => f,
                Node::Raw(_) => panic!("leaf should be a filed element"),
            },
            hashed,
        );

        let (left, right) = self.get_merkle_path(position);

        // create the value for hash
        let mut value = element.to_vec();
        value.resize(4, 0);
        let target = Value::known(Fp::from_raw(value.try_into().unwrap()));

        // create the circuit
        let prover_circuit =
            MerkleExtendedPathEHCircuit::<Fp, PoseidonSpec<W, R>, LM, W, R, LB>::new(
                vec![target],
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

        let public = proof.create_instance(&self.set_commitment);

        // [{(k, hash)}, (r,hash),leaf, index, root]

        #[cfg(debug_assertions)]
        {
            use halo2_proofs::dev::MockProver;
            // over kill k just for test purpose
            let prover = MockProver::run(20, &prover_circuit, vec![public.clone()]).unwrap();
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
        k_commitment: &[u64; 4],
        param: &Params<EqAffine>,
        vk: &VerifyingKey<EqAffine>,
    ) -> Result<bool, String> {
        // verify the k commitment
        proof.verify_k(k_commitment)?;

        let public = proof.create_instance(set_commitment);

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
        println!("k is {k}");

        let pk = keygen_pk(&param, vk, &empty_circuit).expect("keygen_pk should not fail");
        return (param, pk);
    }
}

impl<const LE: usize, const LM: usize, const LB: usize> SHScheme<LE, LM, LB> for Psc<LE, LM, LB> {
    type Element = [u64; LE];
    fn sh_prove_halo(
        &self,
        element: &Self::Element,
        param: &Params<EqAffine>,
        pk: &ProvingKey<EqAffine>,
    ) -> SHProof<LE, LM, LB> {
        const W: usize = 3;
        const R: usize = W - 1;
        let (position, r) = self.get_position_r(element);
        // find the leaf

        let leaf = self.aux[1][position].clone();
        // first we input root
        let mut proof = SHProof::new(
            r,
            self.k.clone(),
            match leaf {
                Node::Field(f) => f,
                _ => panic!("leaf should be a field element"),
            },
        );

        let public = proof.create_instance(&self.set_commitment, element);

        let (left, right) = self.get_merkle_path(position);

        let prover_circuit =
            MerkleExtendedPathSHCircuit::<Fp, PoseidonSpec<W, R>, LM, W, R, LB>::new(
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

        assert_eq![public.len(), LM + 2];

        #[cfg(debug_assertions)]
        {
            use halo2_proofs::dev::MockProver;
            // over kill k just for test purpose
            let prover = MockProver::run(20, &prover_circuit, vec![public.clone()]).unwrap();
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

    fn sh_verify_halo(
        element: &Self::Element,
        proof: &SHProof<LE, LM, LB>,
        set_commitment: &[u8; 32],
        k_commitment: &[u64; 4],
        param: &Params<EqAffine>,
        vk: &VerifyingKey<EqAffine>,
    ) -> Result<bool, String> {
        // verify the k commitment
        proof.verify_k(k_commitment)?;

        let public = proof.create_instance(set_commitment, element);

        assert_eq!(public.len(), LM + 2);

        let membership = proof.get_membership(element);

        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof.proof());
        let strategy = SingleVerifier::new(param);
        // verify the path
        let result = verify_proof(param, vk, strategy, &[&[&public]], &mut transcript);

        match result {
            Ok(_) => Ok(membership),
            Err(error) => panic!("Problem opening the file: {:?}", error),
        }
    }

    fn sh_setup() -> (Params<EqAffine>, ProvingKey<EqAffine>) {
        const POSEIDON_DEGREE: u32 = 7;
        const W: usize = 3;
        const R: usize = W - 1;

        let empty_circuit =
            MerkleExtendedPathSHCircuit::<Fp, PoseidonSpec<W, R>, LM, W, R, LB>::new(
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
        println!("k is {k}");

        let pk = keygen_pk(&param, vk, &empty_circuit).expect("keygen_pk should not fail");
        return (param, pk);
    }
}
