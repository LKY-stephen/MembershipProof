use crate::buckets::Node;
use halo2_gadgets::poseidon::primitives::{self as poseidon, ConstantLength, P128Pow5T3};
use halo2_proofs::pasta::Fp;
use highway::{HighwayHash, HighwayHasher, Key};
use murmurhash3::murmurhash3_x86_32;

pub(crate) fn highwayhash_64<const LE: usize>(key: u64, element: &[u64; LE]) -> u64 {
    let mut hasher = HighwayHasher::new(Key([key, 1, 2, 3]));
    for x in element.iter() {
        hasher.append(&x.to_le_bytes());
    }
    hasher.finalize64()
}

pub(crate) fn highwayhash_default_256(element: &Vec<u64>) -> [u64; 4] {
    let mut hasher = HighwayHasher::default();
    for x in element.iter() {
        hasher.append(&x.to_le_bytes());
    }
    hasher.finalize256()
}

/// for simmilicity we assume there are at most
pub(crate) fn poseidonhash_node(node: &Node) -> Node {
    match node {
        Node::Raw((r, rhs)) => {
            let l = [*r as u64; 4];

            let mut rhs = rhs.to_owned();
            rhs.resize_with(4, || 0);
            Node::Field(poseidonhash(
                Fp::from_raw(l),
                Fp::from_raw(rhs.try_into().unwrap()),
            ))
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

pub fn get_index<const LE: usize>(value: &[u64; LE], r: u32, mask: usize) -> usize {
    let element = value
        .iter()
        .flat_map(|x| x.to_le_bytes())
        .collect::<Vec<_>>();
    murmurhash3_x86_32(&element, r) as usize & mask
}

fn poseidonhash(lhs: Fp, rhs: Fp) -> Fp {
    poseidon::Hash::<_, P128Pow5T3, ConstantLength<2>, 3, 2>::init().hash([lhs, rhs])
}
