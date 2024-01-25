use crate::buckets::Node;
use ff::PrimeField;
use halo2_gadgets::poseidon::primitives::{self as poseidon, ConstantLength, P128Pow5T3};
use halo2_proofs::pasta::Fp;

pub(crate) fn get_top_bits<const LE: usize>(key: u32, element: &[u64; LE], depth: usize) -> usize {
    fp_top_k_bits(get_split_hash(key, element), depth)
}

/// buckket_size must be in form of 2^k
pub(crate) fn get_bucket_index<const LE: usize>(
    element: &[u64; LE],
    rk: u64,
    r: u32,
    bucket_size: usize,
) -> usize {
    fp_mod(get_bucket_hash(rk, r, element), bucket_size - 1)
}

pub(crate) fn get_split_hash<const LE: usize>(key: u32, element: &[u64; LE]) -> Fp {
    let mut rhs = element.to_vec();
    // raw need 4 elements
    rhs.resize_with(4, || 0);
    poseidonhash([Fp::from(key as u64), Fp::from_raw(rhs.try_into().unwrap())])
}

pub(crate) fn get_bucket_hash<const LE: usize>(rk: u64, r: u32, element: &[u64; LE]) -> Fp {
    let mut rhs = element.to_vec();
    // raw need 4 elements
    rhs.resize_with(4, || 0);
    let raw = poseidonhash([Fp::from(rk), Fp::from(r as u64)]);
    poseidonhash([raw, Fp::from_raw(rhs.try_into().unwrap())])
}

pub(crate) fn poseidonhash_node<const LE: usize>(node: &Node) -> Node {
    match node {
        Node::Raw((rk, r, rhs)) => {
            let mut value = rhs.to_owned();
            value.resize_with(4, || 0);
            let raw: Fp = poseidonhash([Fp::from(*rk), Fp::from(*r as u64)]);
            let hash = poseidonhash([raw, Fp::from_raw(value.try_into().unwrap())]);
            Node::Field(hash)
        }
        Node::Field(_) => panic!("No need to hash a field element"),
    }
}

pub(crate) fn poseidon_merkle_hash(lhs: &Node, rhs: &Node) -> Node {
    match (lhs, rhs) {
        (Node::Field(lhs), Node::Field(rhs)) => {
            Node::Field(poseidonhash([lhs.to_owned(), rhs.to_owned()]))
        }
        _ => panic!("poseidonhash: invalid input"),
    }
}

pub fn fp_mod(f: Fp, mask: usize) -> usize {
    f.to_repr().last().expect("should not be empty").to_owned() as usize & mask
}

pub(crate) fn fp_top_k_bits(f: Fp, k: usize) -> usize {
    let element = f.to_repr();

    if k > std::mem::size_of::<usize>() * 8 || k > element.len() * 8 {
        panic!("set is too big") // Return None if k is out of bounds
    }

    let mut result: usize = 0;
    for i in 0..k {
        let byte = element[i / 8];
        let bit = (byte >> (7 - (i % 8))) & 1;
        result = (result << 1) | (bit as usize);
    }
    result
}

fn poseidonhash<const L: usize>(message: [Fp; L]) -> Fp {
    poseidon::Hash::<_, P128Pow5T3, ConstantLength<L>, 3, 2>::init().hash(message)
}
