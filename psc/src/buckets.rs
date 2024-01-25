use std::collections::HashMap;

use crate::hashes::{get_bucket_index, get_top_bits};
use halo2_proofs::pasta::Fp;
use rand::prelude::*;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
#[derive(Clone)]
pub enum Node {
    Raw((u64, u32, Vec<u64>)),
    Field(Fp),
}
pub(crate) struct Buckets<const LE: usize> {
    buckets: Vec<Vec<[u64; LE]>>,
    k: u32,
}

impl<const LE: usize> Buckets<LE> {
    pub(crate) fn new(set: Vec<[u64; LE]>) -> Self {
        Self {
            buckets: vec![set],
            k: 0,
        }
    }

    pub(crate) fn get_k(&self) -> u32 {
        self.k
    }

    pub(crate) fn split(&mut self, set_size: usize, bucket_size: usize) {
        assert_eq!(self.buckets.len(), 1);
        let rng = &mut rand::thread_rng();

        // make sure we have enough buffer to speed up the brute force search
        let mut depth = ((set_size / bucket_size) as f64).log2().round() as usize + 1;

        let mut k = 0;
        let mut counter = 0_u8;
        loop {
            if counter == 100 {
                // increase depth
                counter = 0;

                #[cfg(debug_assertions)]
                println!("cannot find proper k for depth={depth}, increase depth");
                depth += 1;
            }

            let mut hash_map = HashMap::new();
            for (pos, e) in self.buckets[0]
                .par_iter()
                .map(|e| (get_top_bits::<LE>(k, e, depth), e.to_owned()))
                .collect::<Vec<_>>()
            {
                hash_map.entry(pos).or_insert(vec![]).push(e);
            }

            // if this split is good, we will have all buckets with size <= bucket_size
            if hash_map.iter().all(|(_, v)| v.len() <= bucket_size) {
                // we found the k
                let width = 1 << depth;
                let mut vec = vec![];
                for i in 0..width {
                    vec.push(hash_map.entry(i).or_insert(vec![]).to_owned());
                }
                self.buckets = vec;
                self.k = k;
                break;
            }

            // try next k
            k = rng.next_u32();
            counter += 1;
        }
    }

    pub(crate) fn init_aux(&self, bucket_size: usize, rk: u64) -> Vec<Node> {
        let max_set_size = self
            .buckets
            .iter()
            .max_by_key(|x| x.len())
            .expect("empty buckets")
            .len();

        assert!(max_set_size <= bucket_size);

        let leaves = self
            .buckets
            .par_iter()
            .flat_map(|bucket| {
                let mut r = 0_u32;

                // for simplicity, we use (r,r) for empty hole, which is not secure;
                // should use other proper things with different hash instead;
                if bucket.len() == 0 {
                    return vec![Node::Raw((rk, r, vec![r as u64])); bucket_size];
                }
                while r < u32::MAX {
                    let index = bucket
                        .iter()
                        .map(|x| (get_bucket_index(x, rk, r, bucket_size), x))
                        .collect::<HashMap<_, _>>();

                    if index.len() != bucket.len() {
                        // bad r, try next
                        r += 1;
                        continue;
                    }

                    let mut result = vec![];
                    for i in 0..bucket_size {
                        if let Some(&x) = index.get(&i) {
                            result.push(Node::Raw((rk, r, x.to_vec())));
                        } else {
                            result.push(Node::Raw((rk, r, vec![r as u64])));
                        }
                    }
                    return result;
                }

                panic!("can't find r for bucket");
            })
            .collect::<Vec<_>>();

        assert_eq!(leaves.len(), self.buckets.len() * bucket_size);
        return leaves;
    }
}
