mod buckets;
mod hashes;
use crate::buckets::Buckets;
use crate::buckets::Node;
use crate::hashes::*;
use ff::PrimeField;

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
    k: Vec<u64>,
}

pub struct Witness {
    r: u32,
    k: Vec<u64>,
    proof: Vec<Node>,
}

pub trait SetCommitment<const LE: usize, const LM: usize, const LB: usize> {
    type Element;

    fn prove(&self, element: &[u64; LE]) -> Witness;

    fn verify_membership(
        element: &[u64; LE],
        witness: &Witness,
        set_commitment: &[u8; 32],
        k_commitment: &[u64; 4],
    ) -> Result<bool, String>;
}

impl<const LE: usize, const LM: usize, const LB: usize> Psc<LE, LM, LB> {
    const BUCKET_SIZE: usize = 1 << LB;
    const MAX_TREE_DEPTH: usize = LM - LB;
    const MAX_SET_SIZE: usize = 1 << LM;

    pub fn new(set: Vec<[u64; LE]>) -> Self {
        let set_size = set.len();

        if set_size > Self::MAX_SET_SIZE {
            panic!("The size of the set is too large");
        }

        let keys: Vec<[u64; LE]> = set
            .into_iter()
            .map(|x| x.try_into().expect("slice with incorrect length"))
            .collect();

        // initate the vec k.
        let mut buckets = Buckets::new(keys);

        println!("Start spliting");
        buckets.split(set_size, Self::BUCKET_SIZE);

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

        println!("Start maping for buckets");
        let mut aux = vec![buckets.init_aux(Self::BUCKET_SIZE)];
        let raw_leaves = aux.first().expect("empty leaves");
        aux.push(raw_leaves.iter().map(poseidonhash_node).collect());

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
        println!("Start commiting for buckets");
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
}

impl<const LE: usize, const LM: usize, const LB: usize> SetCommitment<LE, LM, LB>
    for Psc<LE, LM, LB>
{
    type Element = [u8; LE];

    fn prove(&self, element: &[u64; LE]) -> Witness {
        let index = self
            .k
            .iter()
            .map(|k| (highwayhash_64(*k, &element) & 1) as usize)
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
        position += get_index(element, r, Self::BUCKET_SIZE - 1);

        // fetch the path
        let mut path = vec![self.aux[1][position].clone()];

        for level in 0..n {
            if position % 2 == 0 {
                path.push(self.aux[level + 1][position + 1].clone());
            } else {
                path.push(self.aux[level + 1][position - 1].clone());
            }
            position /= 2;
        }

        path.reverse();

        Witness {
            r,
            k: self.k.clone(),
            proof: path,
        }
    }

    fn verify_membership(
        element: &[u64; LE],
        witness: &Witness,
        set_commitment: &[u8; 32],
        k_commitment: &[u64; 4],
    ) -> Result<bool, String> {
        // verify the k commitment
        let verified_k = highwayhash_default_256(&witness.k);
        if *k_commitment != verified_k {
            return Err("k_commitment is not correct".to_string());
        }

        let index = witness
            .k
            .iter()
            .map(|k| (highwayhash_64(*k, &element) & 1) == 1)
            .collect::<Vec<_>>();

        // verify the index length
        assert_eq!(index.len(), Self::MAX_TREE_DEPTH);

        // compute bucket index

        let pos = get_index(element, witness.r, Self::BUCKET_SIZE - 1);

        // path before root
        let n = witness.proof.len();

        // remove fake sibiling
        let mut index = index.into_iter().take(n - LB - 1).collect::<Vec<_>>();

        for i in (0..LB).rev() {
            index.push((pos & (1 << i)) != 0); // Use bitwise AND instead of modulo
        }

        // verify the index length, now it should be n-1
        assert_eq!(index.len(), n - 1);

        let leaf = witness.proof[n - 1].clone();
        let my_leaf = poseidonhash_node(&Node::Raw((witness.r.clone(), element.to_vec())));
        let membership = match (my_leaf, leaf.clone()) {
            (Node::Field(input), Node::Field(proved)) => input == proved,
            _ => panic!("Both leaf should be a filed element"),
        };

        // verify the path

        let mut current = leaf;
        // we fetch n-2  elements from the path exclude the root.
        for i in (0..n - 1).rev() {
            let sibiling = &witness.proof[i];
            current = match index[i] {
                false => poseidon_merkle_hash(&current, sibiling),
                true => poseidon_merkle_hash(sibiling, &current),
            };
        }

        if let Node::Field(v_root) = current {
            let computed_commitment = v_root.to_repr();
            if *set_commitment != computed_commitment {
                return Err("set commitment does not match".to_string());
            }
        } else {
            return Err("root is not a field element".to_string());
        }

        Ok(membership)
    }
}
