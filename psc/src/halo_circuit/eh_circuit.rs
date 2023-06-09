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
    S: Spec<F, W, R> + Clone + Copy,
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
    queried: [Value<F>; 1],
    leaf: [Value<F>; 1],
    r: [Value<F>; 1],
    left: Vec<[Value<F>; 1]>,
    right: Vec<[Value<F>; 1]>,
    copy: Vec<Value<F>>,
    _marker: PhantomData<S>,
}

impl<
        F: PrimeField,
        S: Spec<F, W, R> + Clone + Copy,
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
            queried: [Value::unknown(); 1],
            leaf: [Value::unknown(); 1],
            r: [Value::unknown(); 1],
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
        // verify hash of queried for r
        // for k, verify public[3] = hash(k=public[2], queried);

        Self::spliting_check(
            &self.queried[0],
            0,
            1,
            &config,
            &mut layouter.namespace(|| "check queried with  k"),
        )?;

        // public[1] = hash(r=public[0],queried);

        Self::node_check(
            &self.queried[0],
            &self.r[0],
            2,
            &config,
            &mut layouter.namespace(|| "check queried with  r"),
        )?;

        // for r, verify public[4] = hash(r=public[0], leaf);

        Self::node_check(
            &self.leaf[0],
            &self.r[0],
            3,
            &config,
            &mut layouter.namespace(|| "check leaf wit r"),
        )?;

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

            let hash = Self::hash(message, &config, &mut layouter)?;

            left_nodes.push([left]);
            right_nodes.push([right]);
            hash_nodes.push([hash]);
        }

        let merkle_chip = MerkleExtendedPathChip::construct(config.merkle_config.clone());

        // load leave
        merkle_chip.load_leaves(
            &mut layouter,
            left_nodes[0].clone(),
            right_nodes[0].clone(),
            3,
        )?;

        // check root is correct
        layouter.constrain_instance(
            hash_nodes.last().unwrap().to_owned()[0].cell(),
            config.public,
            M + 4,
        )?;

        // check path index is correct
        // position from the second bit
        merkle_chip.load_public_path(
            &mut layouter,
            left_nodes,
            right_nodes,
            hash_nodes,
            &self.copy,
            M,
            B,
            5,
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
        queried: Vec<Value<F>>,
        leaf: Vec<Value<F>>,
        r: Vec<Value<F>>,
        left: Vec<Vec<Value<F>>>,
        right: Vec<Vec<Value<F>>>,
        copy: Vec<Value<F>>,
    ) -> MerkleExtendedPathEHCircuit<F, S, M, W, R, B> {
        assert_eq!(left.len(), right.len());
        assert_eq!(copy.len(), M);
        MerkleExtendedPathEHCircuit {
            queried: queried.try_into().expect("value inputs error"),
            leaf: leaf.try_into().expect("value inputs error"),
            r: r.try_into().expect("value inputs error"),
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

    // check public[result] = hash(seed, element);
    fn node_check(
        element: &Value<F>,
        seed: &Value<F>,
        result_row: usize,
        config: &MerkleExtendedConfig<F, S, M, W, R, B>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let (value, seed) = layouter.assign_region(
            || "load for seed",
            |mut region| {
                let seed = region.assign_advice(
                    || format!("load value "),
                    config.hash_input[0],
                    0,
                    || seed.to_owned(),
                )?;

                let value = region.assign_advice(
                    || format!("load value "),
                    config.hash_input[1],
                    0,
                    || element.to_owned(),
                )?;

                Ok((value, seed))
            },
        )?;

        let message = vec![seed, value.clone()];

        let hash = Self::hash(message, config, layouter)?;

        layouter.constrain_instance(hash.cell(), config.public, result_row)?;
        Ok(())
    }

    // check public[result] = hash(public[seed], element);
    fn spliting_check(
        element: &Value<F>,
        seed_row: usize,
        result_row: usize,
        config: &MerkleExtendedConfig<F, S, M, W, R, B>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let (value, seed) = layouter.assign_region(
            || "load for seed",
            |mut region| {
                let seed = region.assign_advice_from_instance(
                    || format!("load seed"),
                    config.public,
                    seed_row,
                    config.hash_input[0],
                    0,
                )?;
                let value = region.assign_advice(
                    || format!("load value "),
                    config.hash_input[1],
                    0,
                    || element.to_owned(),
                )?;

                Ok((value, seed))
            },
        )?;

        let message = vec![seed, value.clone()];

        let hash = Self::hash(message, config, layouter)?;

        layouter.constrain_instance(hash.cell(), config.public, result_row)?;
        Ok(())
    }

    fn hash(
        message: Vec<AssignedCell<F, F>>,
        config: &MerkleExtendedConfig<F, S, M, W, R, B>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let poseidon_chip = Pow5Chip::construct(config.pow5_config.clone());
        let hasher = Hash::<_, _, S, ConstantLength<2>, W, R>::init(
            poseidon_chip,
            layouter.namespace(|| "init"),
        )?;

        hasher.hash(
            layouter.namespace(|| "hash"),
            message
                .try_into()
                .expect("incorrect length for poseidon inputs"),
        )
    }
}
