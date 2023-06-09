use ff::{Field, PrimeField};
use halo2_proofs::pasta::Fp;

use crate::{
    buckets::Node,
    hashes::{fp_mod, get_bucket_index, get_keyed_hash, get_top_bits, poseidon_merkle_hash},
};

/// internal sturcture to test SC scheme
pub struct Proof<const LE: usize, const LB: usize> {
    r: u32,
    left: Vec<Node>,
    right: Vec<Node>,
}

impl<const LE: usize, const LB: usize> Proof<LE, LB> {
    const BUCKET_SIZE: usize = 1 << LB;

    pub fn new(r: u32, left: Vec<Node>, right: Vec<Node>) -> Self {
        Self { r, left, right }
    }

    pub fn verify(
        &self,
        element: &[u64; LE],
        set_commitment: &[u8; 32],
        k: u32,
    ) -> Result<bool, String> {
        let mut index = vec![];
        let n = self.left.len();
        let bucket_pos = get_top_bits(k, element, n - LB);
        let target = get_keyed_hash(self.r, element);
        let pos = (bucket_pos << LB) + get_bucket_index(element, self.r, Self::BUCKET_SIZE);
        for i in 0..n {
            index.push((pos >> i) & 1);
        }

        let mut current = match index[0] {
            0 => self.left[0].clone(),
            1 => self.right[0].clone(),
            _ => panic!("index should be 0 or 1"),
        };

        let membership = match current {
            Node::Raw(_) => panic!("path should not be a raw value"),
            Node::Field(ref fp) => *fp == target,
        };

        // we fetch n-2  elements from the path exclude the root.
        for i in 0..(n - 1) {
            current = poseidon_merkle_hash(&self.left[i], &self.right[i]);
            let next_layer = match index[i + 1] {
                0 => self.left[i + 1].clone(),
                1 => self.right[i + 1].clone(),
                _ => panic!("index should be 0 or 1"),
            };
            match (current, next_layer) {
                (Node::Field(ref fp), Node::Field(ref fp2)) => {
                    if fp != fp2 {
                        return Err("path is not correct".to_string());
                    }
                }
                _ => {
                    return Err("path has incorrect values".to_string());
                }
            }
        }

        match poseidon_merkle_hash(&self.left[n - 1], &self.right[n - 1]) {
            Node::Field(ref fp) => {
                if *fp != Fp::from_repr(set_commitment.to_owned()).unwrap() {
                    return Err("set_commitment is not correct".to_string());
                }
            }
            _ => {
                panic!("hash return a raw value")
            }
        }

        Ok(membership)
    }
}

pub struct EHProof<const LE: usize, const LM: usize, const LB: usize> {
    k_hashed: Fp,
    r_hashed: Fp,
    on_tree_point: Fp,
    proof: Vec<u8>,
}
impl<const LE: usize, const LM: usize, const LB: usize> EHProof<LE, LM, LB> {
    const BUCKET_MASK: usize = (1 << LB) - 1;
    pub const PUBLIC_SIZE: usize = LM + 5;

    pub fn new(k_hashed: Fp, r_hashed: Fp, on_tree_point: Fp) -> Self {
        Self {
            k_hashed,
            r_hashed,
            on_tree_point,
            proof: vec![],
        }
    }

    pub fn update_proof(&mut self, proof: Vec<u8>) {
        self.proof = proof;
    }

    pub fn get_membership(&self) -> bool {
        self.r_hashed == self.on_tree_point
    }

    /// create the public vector for proof
    /// [k, k_hashed, rhashed, leaf, path, commit]
    pub fn create_instance(&self, set_commitment: &[u8; 32], k: u32) -> Vec<Fp> {
        let mut public = vec![Fp::from_repr(set_commitment.to_owned()).unwrap()];

        // the index of bucket
        let bucket_index = self.k_hashed.to_repr();

        // from high to low
        for i in 0..(LM - LB) {
            public.push(match (bucket_index[i / 8] >> (7 - (i % 8))) & 1 {
                0 => Fp::ZERO,
                1 => Fp::ONE,
                _ => panic!("bit should be 0 or 1"),
            });
        }

        // the index of within bucket
        let bucket_pos = fp_mod(self.r_hashed, Self::BUCKET_MASK);

        // get the in bucket path, from high to low
        for i in (0..LB).rev() {
            public.push(match (bucket_pos >> i) & 1 {
                0 => Fp::ZERO,
                1 => Fp::ONE,
                _ => panic!("bit should be 0 or 1"),
            });
        }

        // push leaf
        public.push(self.on_tree_point);

        public.push(self.r_hashed);
        // push k, kpoint
        public.push(self.k_hashed);

        public.push(Fp::from(k as u64));

        public.reverse();

        assert_eq!(public.len(), Self::PUBLIC_SIZE);
        return public;
    }

    pub fn proof(&self) -> &[u8] {
        self.proof.as_slice()
    }

    pub fn len(&self) -> usize {
        3 * 32 + self.proof.len()
    }
}
