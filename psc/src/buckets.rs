use std::collections::HashMap;

use crate::hashes::highwayhash_64;
use halo2_proofs::pasta::Fp;
use murmurhash3::murmurhash3_x86_32;
use rand::prelude::*;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
#[derive(Clone)]
pub(crate) enum Node {
    Raw((u32, Vec<u64>)),
    Field(Fp),
}
pub(crate) struct Buckets<const LE: usize> {
    buckets: Vec<Vec<[u64; LE]>>,
    k: Vec<u64>,
}

impl<const LE: usize> Buckets<LE> {
    pub(crate) fn new(set: Vec<[u64; LE]>) -> Self {
        Self {
            buckets: vec![set],
            k: vec![],
        }
    }

    pub(crate) fn get_k(&self) -> Vec<u64> {
        self.k.clone()
    }

    pub(crate) fn split(&mut self, set_size: usize, bucket_size: usize) {
        let mut max_set = set_size;
        let rng = &mut rand::thread_rng();

        // make sure we have enough buffer to speed up the brute force search
        // we try for at most 4n set.
        let depth_bound = ((set_size / bucket_size) as f64).log2().round() as usize + 2;

        let mut depth = 0;
        let mut result = self.buckets.clone();
        let mut ks = vec![];
        // split till the bucket size
        while max_set > bucket_size {
            if depth > depth_bound {
                // need to retry
                println!("exceed bound, retry");
                depth = 0;
                result = self.buckets.clone();
                ks = vec![];
            }
            let k = rng.next_u64();
            let splited_buckets = result
                .par_iter()
                .map(|bucket| {
                    let mut splitted = [vec![], vec![]];
                    for element in bucket {
                        let hash = highwayhash_64(k, element);
                        // get the last bit of the second 64-bit word
                        splitted[(hash & 1) as usize].push(element.to_owned());
                    }
                    splitted
                })
                .collect::<Vec<_>>();

            // flatten the splitted buckets
            result = splited_buckets.into_iter().flatten().collect();

            max_set = result
                .iter()
                .max_by_key(|&x| x.len())
                .expect("should not be empty")
                .len();

            ks.push(k);
            depth += 1;

            // println!("max_set_size is {max_set} for the {depth} split");
        }

        self.buckets = result;
        self.k = ks;
    }

    pub(crate) fn init_aux(&self, bucket_size: usize) -> Vec<Node> {
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

                let bucket_u8 = bucket
                    .iter()
                    .map(|x| {
                        let mut bytes = vec![];
                        for i in 0..LE {
                            bytes.extend_from_slice(&x[i].to_le_bytes());
                        }
                        bytes
                    })
                    .collect::<Vec<_>>();

                while r < u32::MAX {
                    let index = bucket_u8
                        .iter()
                        .map(|x| (murmurhash3_x86_32(x, r) as usize & bucket_size - 1, x))
                        .collect::<HashMap<_, _>>();

                    if index.len() != bucket.len() {
                        // bad r, try next
                        r += 1;
                        continue;
                    }

                    let mut result = vec![];
                    for i in 0..bucket_size {
                        if let Some(&x) = index.get(&i) {
                            result.push(Node::Raw((
                                r,
                                x.to_vec()
                                    .chunks(8)
                                    .map(|x| u64::from_le_bytes(x.try_into().unwrap()))
                                    .collect(),
                            )));
                        } else {
                            result.push(Node::Raw((r, vec![r as u64])));
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
