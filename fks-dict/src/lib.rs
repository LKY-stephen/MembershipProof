use num_primes::{BigUint, Verification};
use rs_merkle::{algorithms::Sha256, Hasher, MerkleProof, MerkleTree};
use std::{collections::HashSet, vec};

// FKS dictionary
// The structure store the FKS dictionary and modular p and a
// the first layer hash h1(x)=x*store[0] mod p mod a;
// if h1(x) is not 0:
//   the second layer hash h2(x) = x*store[h1[x]+1] mod p mod store[h1[x]]
// The implementation is not fully optmized for space usage.
/*
 WARNING
 1. We use u32 to store elements, in worst case each u32 element needs
 6 times space for achieving o(1) access.
 Users should use this implementation no more than around 2^29( around 536 million) u32 elements.
 2. The modular p is also an u32 elements, hence the max value is around
 4,294,967,290 (4,294,967,291 is the biggest prime of u32)
 3. zero is used for not exist element, hence do not insert into the dictionary.
*/

pub struct FKSDict {
    p: u32,
    a: u32,
    store: Vec<u32>,
}

impl FKSDict {
    pub fn new(input: &HashSet<u32>, max: u32) -> FKSDict {
        let n: u32 = input.len() as u32;
        // smallest prime bigger than max
        let mut p = if (max & 1) == 0 { max + 1 } else { max };
        while Verification::is_composite(&BigUint::from(p)) {
            p += 2;
        }

        // Init first layer hash
        let mut group: Vec<HashSet<u32>>;
        let mut k = 1;

        loop {
            group = compute_collision(input, k, p, n);
            let mut sum = 0;
            for x in group.iter() {
                let l = x.len();
                sum += l * l;
            }
            if sum > (3 * n) as usize {
                k += 1;
                continue;
            }
            break;
        }

        // Fill dictionary
        let mut dict: Vec<u32> = Vec::new();
        dict.push(k);
        let mut w: Vec<u32> = Vec::new();

        let mut pointer = n + 1;
        for x in group.iter() {
            let s: u32 = (x.len()) as u32;
            if s > 0 {
                let w_size: u32 = s * s;
                w.push(w_size);
                let mut k2 = 1;
                // Fill the second layer
                loop {
                    let subgroup = compute_collision(x, k2, p, w_size);

                    if (&subgroup).into_iter().any(|z| z.len() > 1) {
                        k2 += 1;
                        continue;
                    }

                    w.push(k2);
                    for e in subgroup.iter() {
                        if e.is_empty() {
                            w.push(0);
                        } else {
                            w.push(*e.iter().next().unwrap() as u32);
                        }
                    }
                    break;
                }

                dict.push(pointer);
                pointer += w_size + 2;
            } else {
                dict.push(0)
            }
        }
        assert_eq!(dict.len(), 1 + n as usize);
        assert_eq!(dict.len() + w.len(), pointer as usize);
        dict.append(&mut w);
        return FKSDict {
            p: p,
            a: n,
            store: dict,
        };
    }

    // Query if an element is stored in the dictionary
    pub fn query(&self, x: u32) -> bool {
        self.do_query(x).ends_with(&[x])
    }

    // verify if an membership apply to the dictionary
    // return err if the query is incorrect
    // return ok(bool for results)
    pub fn verify(&self, x: u32, query: &[u32]) -> Result<bool, ()> {
        if query[2] != self.store[0]
            || query[0] != self.p
            || query[1] != self.a
            || query[3] != self.store[1 + perfect_hash(x, query[2], query[0], query[1]) as usize]
        {
            return Err(());
        }

        if query[3] == 0 {
            if query.len() == 4 {
                return Ok(false);
            }
        }

        if query[4] != self.store[query[3] as usize]
            || query[5] != self.store[1 + query[3] as usize]
            || query[6]
                != self.store
                    [(2 + query[3] + perfect_hash(x, query[5], query[0], query[4])) as usize]
        {
            return Err(());
        }

        return Ok(query[6] == x);

        // non exist memproof
    }

    // build merkle tree from ref, q, a, store.
    pub fn commit(&self, refer: &Vec<u32>) -> [u8; 32] {
        return self.build_tree(refer).root().unwrap();
    }

    // generate a merkle tree proof for refer and query result
    pub fn gen_proof(&self, x: u32, refer: &Vec<u32>) -> (Vec<u8>, Vec<u32>) {
        let mut query = self.do_query(x);
        let tree = self.build_tree(refer);
        let r = refer.len();
        let index: Vec<usize> = query_proof_index(r as u32, x, &query);

        query.push((self.store.len() + r + 2) as u32);

        (tree.proof(&index).to_bytes(), query)
    }

    // Generate a constant size query for (non)-membership
    // p, a, k, w, r, k2, v
    pub fn do_query(&self, x: u32) -> Vec<u32> {
        let h1 = perfect_hash(x, self.store[0], self.p, self.a) + 1;
        let w = self.store[h1 as usize];
        if w == 0 {
            return vec![self.p, self.a, self.store[0], 0];
        };
        let k2: u32 = self.store[1 + w as usize];
        let r: u32 = self.store[w as usize];

        let y = perfect_hash(x, k2, self.p, r);

        return vec![
            self.p,
            self.a,
            self.store[0],
            w,
            r,
            k2,
            self.store[(2 + w + y) as usize],
        ];
    }

    // tree from refer, p, a, store
    fn build_tree(&self, refer: &Vec<u32>) -> MerkleTree<Sha256> {
        let mut dataset = refer.to_owned();
        dataset.push(self.p);
        dataset.push(self.a);
        dataset.append(&mut self.store.to_owned());
        let leaves: Vec<[u8; 32]> = dataset
            .iter()
            .map(|x| Sha256::hash(x.to_string().as_bytes()))
            .collect();

        MerkleTree::from_leaves(&leaves)
    }
}

// Verify if a proof is correct or not
// 1. check if proof is well formed
// 2. check if proof is correct for refer and commit
// 3. check if the hash in proof is correctly calculated for x
// 4. return the query result of the proof
pub fn verify_commit_proof(
    x: u32,
    refer: &Vec<u32>,
    proof: &(Vec<u8>, Vec<u32>),
    commit: &[u8; 32],
) -> Result<bool, &'static str> {
    let n = proof.1.len();

    let r = refer.len();

    // <refer>, p,a,k,w,r,k2,v
    let mut query = proof.1[0..n - 1].to_owned();
    let mut leaves = refer.to_owned();
    leaves.append(&mut query);

    let leaves_hash: Vec<[u8; 32]> = leaves
        .iter()
        .map(|x| Sha256::hash(x.to_string().as_bytes()))
        .collect();
    let index = query_proof_index(r as u32, x, &proof.1[0..n - 1].to_vec());

    let merkle_proof = MerkleProof::<Sha256>::try_from(proof.0.to_owned());

    if merkle_proof.is_err() {
        return Err("Incorrect merkle proof");
    }

    if !merkle_proof.unwrap().verify(
        commit.to_owned(),
        index.as_slice(),
        leaves_hash.as_slice(),
        proof.1[n - 1] as usize,
    ) {
        return Err("merkle tree verification failed");
    }

    if index[r + 3] != r + 3 + perfect_hash(x, proof.1[2], proof.1[0], proof.1[1]) as usize {
        return Err("first layer hash is incorrect");
    }

    if n == r + 6
        && index[r + 6]
            != r + 4
                + proof.1[3] as usize
                + perfect_hash(x, proof.1[5], proof.1[0], proof.1[4]) as usize
    {
        return Err("second layer hash is incorrect");
    }
    return Ok(proof.1[n - 2] == x);
}

fn compute_collision(input: &HashSet<u32>, k: u32, p: u32, a: u32) -> Vec<HashSet<u32>> {
    let mut v = vec![HashSet::new(); a as usize];
    for x in input.iter() {
        v[perfect_hash(*x, k, p, a) as usize].insert(*x);
    }
    return v;
}

fn perfect_hash(x: u32, k: u32, p: u32, a: u32) -> u32 {
    let y = ((x as u64 * k as u64) % p as u64) as u32;
    return y % a;
}

// index of reference, p, a, k, w, r, k2, v in leaves
fn query_proof_index(referlen: u32, x: u32, query: &Vec<u32>) -> Vec<usize> {
    // start point of store

    let starter = referlen + 2;

    // index for refer
    let mut index: Vec<u32> = (0..referlen).collect();

    // index for k, p, a
    index.append(&mut vec![referlen, referlen + 1, starter]);

    // prove first store[h1(x)] =  1
    index.push(starter + 1 + perfect_hash(x, query[2], query[0], query[1]));

    if query.len() == 7 {
        // prove second layer parameters
        index.push(starter + query[3]);
        index.push(starter + 1 + query[3]);

        // index of query[6]
        index.push(starter + 2 + query[3] + perfect_hash(x, query[5], query[0], query[4]));
    }

    return index.into_iter().map(|x| x as usize).collect();
}
