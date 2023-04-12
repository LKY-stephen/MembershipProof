use ff::{Field, PrimeField};
use halo2_proofs::pasta::Fp;

use crate::{
    buckets::Node,
    hashes::{
        fp_mod, get_bucket_index, get_k_index, get_keyed_hash, highwayhash_default_256,
        poseidon_merkle_hash,
    },
};

/// internal sturcture to test SC scheme
pub struct Proof<const LE: usize, const LB: usize> {
    r: u32,
    k: Vec<u32>,
    left: Vec<Node>,
    right: Vec<Node>,
}

impl<const LE: usize, const LB: usize> Proof<LE, LB> {
    const BUCKET_MASK: usize = (1 << LB) - 1;

    pub fn new(r: u32, k: Vec<u32>, left: Vec<Node>, right: Vec<Node>) -> Self {
        Self { r, k, left, right }
    }

    pub fn verify_k(&self, k_commitment: &[u64; 4]) -> Result<(), String> {
        let verified_k = highwayhash_default_256(&self.k);
        if *k_commitment != verified_k {
            return Err("k_commitment is not correct".to_string());
        }
        Ok(())
    }

    pub fn verify(&self, element: &[u64; LE], set_commitment: &[u8; 32]) -> Result<bool, String> {
        let mut index = vec![];
        let n = self.left.len();
        for i in 0..(n - LB) {
            index.push(get_k_index(self.k[i], element));
        }

        let target = get_keyed_hash(self.r, element);
        let pos = fp_mod(target, Self::BUCKET_MASK);

        // get the bucket index
        for i in (0..LB).rev() {
            index.push((pos >> i) & 1);
        }

        index.reverse();

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

pub struct SHProof<const LE: usize, const LM: usize, const LB: usize> {
    r: u32,
    k: Vec<u32>,
    f: Fp,
    proof: Vec<u8>,
}

impl<const LE: usize, const LM: usize, const LB: usize> SHProof<LE, LM, LB> {
    const BUCKET_MASK: usize = (1 << LB) - 1;
    pub const PUBLIC_SIZE: usize = LM + 2;

    pub fn new(r: u32, k: Vec<u32>, f: Fp) -> Self {
        assert_eq!(k.len(), LM - LB);
        Self {
            r,
            k,
            f,
            proof: vec![],
        }
    }

    pub fn update_proof(&mut self, proof: Vec<u8>) {
        self.proof = proof;
    }

    pub fn verify_k(&self, k_commitment: &[u64; 4]) -> Result<(), String> {
        let verified_k = highwayhash_default_256(&self.k);
        if *k_commitment != verified_k {
            return Err("k_commitment is not correct".to_string());
        }
        Ok(())
    }

    pub fn get_membership(&self, element: &[u64; LE]) -> bool {
        let target = get_keyed_hash(self.r, element);
        target == self.f
    }

    pub fn create_instance(&self, set_commitment: &[u8; 32], element: &[u64; LE]) -> Vec<Fp> {
        let mut public = vec![Fp::from_repr(set_commitment.to_owned()).unwrap()];

        for &k in self.k.iter() {
            public.push(match get_k_index(k, element) {
                0 => Fp::ZERO,
                1 => Fp::ONE,
                _ => panic!("bit should be 0 or 1"),
            });
        }

        // compute bucket index

        let pos = get_bucket_index(element, self.r, Self::BUCKET_MASK);

        // get the final path
        for i in (0..LB).rev() {
            public.push(match (pos >> i) & 1 {
                0 => Fp::ZERO,
                1 => Fp::ONE,
                _ => panic!("bit should be 0 or 1"),
            });
        }

        public.push(self.f.clone());

        public.reverse();

        assert_eq!(public.len(), Self::PUBLIC_SIZE);

        public
    }

    pub fn proof(&self) -> &[u8] {
        self.proof.as_slice()
    }

    pub fn len(&self) -> usize {
        (1 + self.k.len()) * 4 + 8 + self.proof.len()
    }
}

pub struct EHProof<const LE: usize, const LM: usize, const LB: usize> {
    r: u32,
    k: Vec<u32>,
    hashed: Vec<Fp>,
    f: Fp,
    proof: Vec<u8>,
}
impl<const LE: usize, const LM: usize, const LB: usize> EHProof<LE, LM, LB> {
    const BUCKET_MASK: usize = (1 << LB) - 1;
    pub const PUBLIC_SIZE: usize = LM + 2 + 2 * (LM - LB + 1);

    pub fn new(r: u32, k: Vec<u32>, f: Fp, hashed: Vec<Fp>) -> Self {
        assert_eq!(k.len() + 1, hashed.len());
        assert_eq!(k.len(), LM - LB);
        Self {
            r,
            k,
            hashed,
            f,
            proof: vec![],
        }
    }

    pub fn update_proof(&mut self, proof: Vec<u8>) {
        self.proof = proof;
    }

    pub fn verify_k(&self, k_commitment: &[u64; 4]) -> Result<(), String> {
        let verified_k = highwayhash_default_256(&self.k);
        if *k_commitment != verified_k {
            return Err("k_commitment is not correct".to_string());
        }
        Ok(())
    }

    pub fn get_membership(&self) -> bool {
        let target = self.hashed.last().expect("hashed is empty").clone();
        target == self.f
    }

    pub fn create_instance(&self, set_commitment: &[u8; 32]) -> Vec<Fp> {
        let mut public = vec![Fp::from_repr(set_commitment.to_owned()).unwrap()];
        let target = self.hashed.last().expect("hashed is empty").clone();

        let mut pub_kr = vec![];
        for i in 0..(LM - LB) {
            public.push(match fp_mod(self.hashed[i], 1) {
                0 => Fp::ZERO,
                1 => Fp::ONE,
                _ => panic!("bit should be 0 or 1"),
            });

            pub_kr.push(Fp::from(self.k[i] as u64));
            pub_kr.push(self.hashed[i]);
        }

        // compute bucket index from target

        let pos = fp_mod(target, Self::BUCKET_MASK);

        // get the final path
        for i in (0..LB).rev() {
            public.push(match (pos >> i) & 1 {
                0 => Fp::ZERO,
                1 => Fp::ONE,
                _ => panic!("bit should be 0 or 1"),
            });
        }

        // push leaf
        public.push(self.f);

        // push target
        public.push(target);

        public.push(Fp::from(self.r as u64));

        public.reverse();

        assert_eq!(public.len() + pub_kr.len(), Self::PUBLIC_SIZE);

        pub_kr.into_iter().chain(public).collect()
    }

    pub fn proof(&self) -> &[u8] {
        self.proof.as_slice()
    }

    pub fn len(&self) -> usize {
        (1 + self.k.len()) * 4 + (self.hashed.len() + 1) * 8 + self.proof.len()
    }
}
