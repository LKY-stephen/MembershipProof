use crate::buckets::Node;
use ff::PrimeField;
use halo2_gadgets::poseidon::primitives::{self as poseidon, ConstantLength, P128Pow5T3};
use halo2_proofs::pasta::Fp;
use highway::{HighwayHash, HighwayHasher};

pub(crate) fn get_k_index<const LE: usize>(key: u32, element: &[u64; LE]) -> usize {
    fp_mod(get_keyed_hash(key, element), 1)
}

pub fn get_bucket_index<const LE: usize>(element: &[u64; LE], r: u32, mask: usize) -> usize {
    fp_mod(get_keyed_hash(r, element), mask)
}

pub(crate) fn get_keyed_hash<const LE: usize>(key: u32, element: &[u64; LE]) -> Fp {
    let mut rhs = element.to_vec();
    rhs.resize_with(4, || 0);
    poseidonhash(Fp::from(key as u64), Fp::from_raw(rhs.try_into().unwrap()))
}

pub(crate) fn highwayhash_default_256(element: &Vec<u32>) -> [u64; 4] {
    let mut hasher = HighwayHasher::default();
    for x in element.iter() {
        hasher.append(&x.to_le_bytes());
    }
    hasher.finalize256()
}

/// for simmilicity we assume there are at most
pub(crate) fn poseidonhash_node<const LE: usize>(node: &Node) -> Node {
    match node {
        Node::Raw((r, rhs)) => {
            let mut value = rhs.to_owned();
            value.resize(LE, 0);
            let hash = get_keyed_hash::<LE>(*r, &value.try_into().unwrap());
            Node::Field(hash)
        }
        Node::Field(_) => panic!("No need to hash a field element"),
    }
}

pub(crate) fn poseidon_merkle_hash(lhs: &Node, rhs: &Node) -> Node {
    match (lhs, rhs) {
        (Node::Field(lhs), Node::Field(rhs)) => {
            Node::Field(poseidonhash(lhs.to_owned(), rhs.to_owned()))
        }
        _ => panic!("poseidonhash: invalid input"),
    }
}

pub fn fp_mod(f: Fp, mask: usize) -> usize {
    f.to_repr().last().expect("should not be empty").to_owned() as usize & mask
}

fn poseidonhash(lhs: Fp, rhs: Fp) -> Fp {
    poseidon::Hash::<_, P128Pow5T3, ConstantLength<2>, 3, 2>::init().hash([lhs, rhs])
}
