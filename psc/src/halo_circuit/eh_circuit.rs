use super::merkle_chip::{MerkleExtendedPathChip, MerkleExtendedPathInstruction, MerklePathConfig};
use std::marker::PhantomData;

use ff::PrimeField;
use halo2_gadgets::poseidon::primitives::{ConstantLength, Spec};
use halo2_gadgets::poseidon::{Hash, Pow5Chip, Pow5Config};
use halo2_proofs::circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance};

#[derive(Clone)]
pub struct MerkleExtendedConfig<
    F: PrimeField,
    S: Spec<F, W, R> + Clone,
    const M: usize,
    const W: usize,
    const R: usize,
    const B: usize,
> {
    // we use halo_2's gadget, hence we can only use hash output as one element
    merkle_config: MerklePathConfig<1>,
    pow5_config: Pow5Config<F, W, R>,
    hash_input: [Column<Advice>; R],
    public: Column<Instance>,
    _marker: PhantomData<S>,
}

// implementation for 5-posiedon
// For each input, we fixed the padding as [x,1,0,0,...,0]
// inputs permutation rounds will go for all abosrb
#[derive(Clone, Default)]
pub struct MerkleExtendedPathEHCircuit<
    F: PrimeField,
    S: Spec<F, W, R>,
    const M: usize,
    const W: usize,
    const R: usize,
    const B: usize,
> {
    value: [Value<F>; 1],
    left: Vec<[Value<F>; 1]>,
    right: Vec<[Value<F>; 1]>,
    copy: Vec<Value<F>>,
    _marker: PhantomData<S>,
}

impl<
        F: PrimeField,
        S: Spec<F, W, R> + Clone,
        const M: usize,
        const W: usize,
        const R: usize,
        const B: usize,
    > Circuit<F> for MerkleExtendedPathEHCircuit<F, S, M, W, R, B>
{
    type Config = MerkleExtendedConfig<F, S, M, W, R, B>;

    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            value: [Value::unknown(); 1],
            left: vec![[Value::unknown(); 1]; M + 1],
            right: vec![[Value::unknown(); 1]; M + 1],
            copy: vec![Value::unknown(); M + 1],
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let value = meta.advice_column();
        let copy_flag = meta.advice_column();
        let index_flag = meta.advice_column();

        // public column for output
        let output = meta.instance_column();

        meta.enable_equality(output);
        let state = (0..W).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let partial_sbox = meta.advice_column();

        let rc_a = (0..W).map(|_| meta.fixed_column()).collect::<Vec<_>>();
        let rc_b = (0..W).map(|_| meta.fixed_column()).collect::<Vec<_>>();

        meta.enable_constant(rc_b[0]);

        MerkleExtendedConfig {
            merkle_config: MerkleExtendedPathChip::configure(
                meta,
                [value],
                copy_flag,
                index_flag,
                output,
            ),
            hash_input: state[..R].try_into().unwrap(),
            public: output,
            pow5_config: Pow5Chip::configure::<S>(
                meta,
                state.try_into().unwrap(),
                partial_sbox,
                rc_a.try_into().unwrap(),
                rc_b.try_into().unwrap(),
            ),
            _marker: PhantomData,
        }
    }

    fn synthesize(
        &self,
        config: MerkleExtendedConfig<F, S, M, W, R, B>,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let merkle_chip = MerkleExtendedPathChip::construct(config.merkle_config.clone());

        // handle path
        let copy_len = M - self.left.len();
        let padded_left = self.left[..B]
            .to_owned()
            .into_iter()
            .chain(vec![self.left[B - 1].clone(); copy_len])
            .chain(self.left[B..].to_owned())
            .collect::<Vec<_>>();
        let padded_right = self.right[..B]
            .to_owned()
            .into_iter()
            .chain(vec![self.right[B - 1].clone(); copy_len])
            .chain(self.right[B..].to_owned())
            .collect::<Vec<_>>();
        let mut left_nodes = vec![];
        let mut right_nodes = vec![];
        let mut hash_nodes: Vec<[AssignedCell<F, F>; 1]> = vec![];

        // compute hash
        for row in 0..M {
            let poseidon_chip = Pow5Chip::construct(config.pow5_config.clone());
            let (left, right) = layouter.assign_region(
                || "load message",
                |mut region| {
                    let left = region.assign_advice(
                        || format!("load left node at row {row}"),
                        config.hash_input[0],
                        0,
                        || padded_left[row][0],
                    )?;

                    let right = region.assign_advice(
                        || format!("load right node at row {row}"),
                        config.hash_input[1],
                        0,
                        || padded_right[row][0],
                    )?;

                    Ok((left, right))
                },
            )?;
            let message = vec![left.clone(), right.clone()];
            let hasher = Hash::<_, _, S, ConstantLength<2>, W, R>::init(
                poseidon_chip,
                layouter.namespace(|| "init"),
            )?;

            let hash = hasher.hash(
                layouter.namespace(|| "hash"),
                message
                    .try_into()
                    .expect("incorrect length for poseidon inputs"),
            )?;

            left_nodes.push([left]);
            right_nodes.push([right]);
            hash_nodes.push(
                vec![hash]
                    .try_into()
                    .expect("incorrect length for poseidon left inputs"),
            );
        }

        let leaf_value = self.value;

        // verify hash of r
        let poseidon_chip = Pow5Chip::construct(config.pow5_config.clone());
        let (leaf_value, r) = layouter.assign_region(
            || "load for r",
            |mut region| {
                let r = region.assign_advice_from_instance(
                    || format!("load r"),
                    config.public,
                    2 * (M - B),
                    config.hash_input[0],
                    0,
                )?;
                let value = region.assign_advice(
                    || format!("load value "),
                    config.hash_input[1],
                    0,
                    || leaf_value[0],
                )?;

                Ok((value, r))
            },
        )?;

        let message = vec![r, leaf_value.clone()];
        let hasher = Hash::<_, _, S, ConstantLength<2>, W, R>::init(
            poseidon_chip,
            layouter.namespace(|| "init"),
        )?;

        let hash = hasher.hash(
            layouter.namespace(|| "hash"),
            message
                .try_into()
                .expect("incorrect length for poseidon inputs"),
        )?;

        // public[1] = hash(r=public[0],value);
        layouter.constrain_instance(hash.cell(), config.public, 2 * (M - B) + 1)?;

        // for all k, verify public[2*row+3] = hash(k=public[2*row], value);
        for row in 0..(M - B) {
            let poseidon_chip = Pow5Chip::construct(config.pow5_config.clone());
            let (value, k) = layouter.assign_region(
                || "load for para",
                |mut region| {
                    let value = leaf_value.clone().copy_advice(
                        || format!("load value for row {row}"),
                        &mut region,
                        config.hash_input[0],
                        0,
                    )?;

                    let k = region.assign_advice_from_instance(
                        || format!("load k node at row {row}"),
                        config.public,
                        2 * row,
                        config.hash_input[1],
                        0,
                    )?;

                    Ok((value, k))
                },
            )?;
            let message = vec![k, value];
            let hasher = Hash::<_, _, S, ConstantLength<2>, W, R>::init(
                poseidon_chip,
                layouter.namespace(|| "init"),
            )?;

            let hash = hasher.hash(
                layouter.namespace(|| "hash"),
                message
                    .try_into()
                    .expect("incorrect length for poseidon inputs"),
            )?;

            // public[1] = hash(r=public[0],value);
            layouter.constrain_instance(hash.cell(), config.public, 2 * row + 1)?;
        }

        let position = 2 * (M - B + 1);
        merkle_chip.load_leaves(
            &mut layouter,
            left_nodes[0].clone(),
            right_nodes[0].clone(),
            position,
        )?;

        // check root is correct
        layouter.constrain_instance(
            hash_nodes.last().expect("no empty hash")[0].cell(),
            config.public,
            3 * (M + 1) - 2 * B,
        )?;

        // check path index is correct
        merkle_chip.load_public_path(
            &mut layouter,
            left_nodes,
            right_nodes,
            hash_nodes,
            &self.copy,
            M,
            B,
            position + 2,
        )?;
        return Ok(());
    }
}

impl<
        F: PrimeField,
        S: Spec<F, W, R> + Clone + Copy,
        const M: usize,
        const W: usize,
        const R: usize,
        const B: usize,
    > MerkleExtendedPathEHCircuit<F, S, M, W, R, B>
{
    /// input the real path
    /// [left leave, right leave]
    /// [left node, right node]
    /// ...
    /// [root, root]
    pub fn new(
        value: Vec<Value<F>>,
        left: Vec<Vec<Value<F>>>,
        right: Vec<Vec<Value<F>>>,
        copy: Vec<Value<F>>,
    ) -> MerkleExtendedPathEHCircuit<F, S, M, W, R, B> {
        assert_eq!(left.len(), right.len());
        assert_eq!(copy.len(), M);
        MerkleExtendedPathEHCircuit {
            value: value.try_into().expect("value inputs error"),
            left: left
                .into_iter()
                .map(|v| v.try_into().expect("left inputs error"))
                .collect(),
            right: right
                .into_iter()
                .map(|v| v.try_into().expect("right inputs error"))
                .collect(),
            copy: copy,
            _marker: PhantomData,
        }
    }
}
