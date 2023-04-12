// Since we need to verify the hash computation
// The constraints will be an extension to the poseidon_chip's
// with additional merkle related constraints.

use std::{marker::PhantomData, vec};

use ff::PrimeField;
use halo2_proofs::{
    circuit::{AssignedCell, Chip, Layouter, Region, Value},
    plonk::{
        Advice, Column, ConstraintSystem, Constraints, Error,
        Expression::{self},
        Instance, Selector,
    },
    poly::Rotation,
};

#[derive(Debug, Clone)]
pub struct Node<F: PrimeField, const I: usize>([AssignedCell<F, F>; I]);

pub trait MerkleExtendedPathInstruction<F: PrimeField, const I: usize>: Chip<F> {
    /// Variable representing a tree node
    type Node;

    /// Loads a left child, a right child and paths
    /// copy only works from b to m
    fn load_public_path(
        &self,
        layouter: &mut impl Layouter<F>,
        left: Vec<[AssignedCell<F, F>; I]>,
        right: Vec<[AssignedCell<F, F>; I]>,
        hash: Vec<[AssignedCell<F, F>; I]>,
        copy: &Vec<Value<F>>,
        len: usize,
        b: usize,
        position: usize,
    ) -> Result<(), Error>;

    /// Loads a left child, a right child
    /// return a node of its selection according to
    /// index
    fn load_leaves(
        &self,
        layouter: &mut impl Layouter<F>,
        left: [AssignedCell<F, F>; I],
        right: [AssignedCell<F, F>; I],
        position: usize,
    ) -> Result<(), Error>;

    /// check the final result with index
    fn expose_public(
        &self,
        layouter: &mut impl Layouter<F>,
        num: Self::Node,
        row: usize,
    ) -> Result<(), Error>;
}

pub struct MerkleExtendedPathChip<F: PrimeField, const I: usize> {
    config: MerklePathConfig<I>,
    _marker: PhantomData<F>,
}

///
/// The chip handles three
#[derive(Clone, Debug)]
pub struct MerklePathConfig<const I: usize> {
    /// private input for element
    value: [Column<Advice>; I],

    /// flag for hash and copy
    copy_flag: Column<Advice>,

    /// flag for left child or right child
    index_flag: Column<Advice>,

    /// This is the public input (instance) column.
    public: Column<Instance>,

    /// selector for hash query
    s_bucket: Selector,

    /// selector for copy_hash query
    s_chash: Selector,

    /// selector for hash query
    s_pub: Selector,
}

impl<F: PrimeField, const I: usize> MerkleExtendedPathChip<F, I> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        value: [Column<Advice>; I],
        copy_flag: Column<Advice>,
        index_flag: Column<Advice>,
        public: Column<Instance>,
    ) -> <Self as Chip<F>>::Config {
        // equality checks for output and internal states
        for i in 0..I {
            meta.enable_equality(value[i]);
        }
        meta.enable_equality(public);
        meta.enable_equality(index_flag);

        let s_hash = meta.selector();
        let s_pub = meta.selector();
        let s_chash = meta.selector();

        let one = Expression::Constant(F::ONE);
        let bool_constraint = |v: Expression<F>| v.clone() * (one.clone() - v);

        // from layer b, we may copy the path for some times, therefore, we use
        // the copy row to identify which row we are copying.
        // the last n row do not need to copy, hence the copy flag should be
        // 1 for b to m-n rows
        let copy_flag_constraint =
            |before: Expression<F>, after: Expression<F>| after * (one.clone() - before);
        // constraints the hash and copy constraints
        meta.create_gate("Bucket_Hash", |meta| {
            let s_hash = meta.query_selector(s_hash);

            // we store values as
            // value         copy      index      s_hash
            // left           -          -          0
            // right          -          -          0
            // hash           -         0/1         1
            // next left      -          -          0
            // next right     -          -          0

            let p_hash_v = (0..I)
                .map(|i| meta.query_advice(value[i], Rotation::cur()))
                .collect::<Vec<_>>();

            let index = meta.query_advice(index_flag, Rotation::cur());

            let left_v = (0..I)
                .map(|i| meta.query_advice(value[i], Rotation::next()))
                .collect::<Vec<_>>();

            let right_v = (0..I)
                .map(|i| meta.query_advice(value[i], Rotation(2)))
                .collect::<Vec<_>>();

            // (1-copy)*(p_hash - (1-index)*left -index * right) is the hash constraint

            let hash_constraint = (0..I)
                .map(|i| {
                    p_hash_v[i].clone()
                        - (one.clone() - index.clone()) * left_v[i].clone()
                        - index.clone() * right_v[i].clone()
                })
                .collect::<Vec<_>>();

            let constraints = vec![bool_constraint(index)]
                .into_iter()
                .chain(hash_constraint);
            Constraints::with_selector(s_hash, constraints)
        });
        // constraints the hash and copy constraints
        meta.create_gate("Copy_Hash", |meta| {
            let s_chash = meta.query_selector(s_chash);

            // we store values as
            // value         copy      index      s_hash
            // left           -          -          0
            // right          -          -          0
            // hash          0/1        0/1         1
            // next left      -          -          0
            // next right     -          -          0

            let p_left_v = (0..I)
                .map(|i| meta.query_advice(value[i], Rotation(-2)))
                .collect::<Vec<_>>();

            let p_right_v = (0..I)
                .map(|i| meta.query_advice(value[i], Rotation::prev()))
                .collect::<Vec<_>>();

            let p_hash_v = (0..I)
                .map(|i| meta.query_advice(value[i], Rotation::cur()))
                .collect::<Vec<_>>();

            let n_copy = meta.query_advice(copy_flag, Rotation(3));
            let copy = meta.query_advice(copy_flag, Rotation::cur());
            let index = meta.query_advice(index_flag, Rotation::cur());

            let left_v = (0..I)
                .map(|i| meta.query_advice(value[i], Rotation::next()))
                .collect::<Vec<_>>();

            let right_v = (0..I)
                .map(|i| meta.query_advice(value[i], Rotation(2)))
                .collect::<Vec<_>>();

            // copy is zero until some point it becomes one (p_copy*(1-copy)).
            // index is bool value
            // (1-copy)*(p_hash - (1-index)*left -index * right) is the hash constraint
            // copy*((1-index)*(p_left-left) + (index) (p_right - right)) is the copy constraint

            let hash_constraint = (0..I)
                .map(|i| {
                    (one.clone() - copy.clone())
                        * (p_hash_v[i].clone()
                            - (one.clone() - index.clone()) * left_v[i].clone()
                            - index.clone() * right_v[i].clone())
                })
                .collect::<Vec<_>>();
            let copy_constraint = (0..I)
                .map(|i| {
                    copy.clone()
                        * ((one.clone() - index.clone())
                            * (p_left_v[i].clone() - left_v[i].clone())
                            + index.clone() * (p_right_v[i].clone() - right_v[i].clone()))
                })
                .collect::<Vec<_>>();

            let constraints = vec![
                bool_constraint(n_copy.clone()),
                bool_constraint(copy.clone()),
                copy_flag_constraint(copy.clone(), n_copy.clone()),
                bool_constraint(index),
            ]
            .into_iter()
            .chain(hash_constraint)
            .chain(copy_constraint);
            Constraints::with_selector(s_chash, constraints)
        });

        // constraints the hash and copy for the first layer inputs
        meta.create_gate("PUB_SELECT", |meta| {
            let s_pub = meta.query_selector(s_pub);

            // we store values as
            // value         copy      index      s_pub
            // left           -          -          0
            // right          -          -          0
            // hash          0/1        0/1         1

            let left_v = (0..I)
                .map(|i| meta.query_advice(value[i], Rotation(-2)))
                .collect::<Vec<_>>();

            let right_v = (0..I)
                .map(|i| meta.query_advice(value[i], Rotation::prev()))
                .collect::<Vec<_>>();

            let hash_v = (0..I)
                .map(|i| meta.query_advice(value[i], Rotation::cur()))
                .collect::<Vec<_>>();

            let index = meta.query_advice(index_flag, Rotation::cur());
            let copy = meta.query_advice(copy_flag, Rotation::cur());

            // copy left to hash if index is 0 other wise copy the right one

            let copy_constraint = (0..I)
                .map(|i| {
                    (one.clone() - index.clone()) * (left_v[i].clone() - hash_v[i].clone())
                        + index.clone() * (right_v[i].clone() - hash_v[i].clone())
                })
                .collect::<Vec<_>>();

            let constraints = vec![bool_constraint(index.clone()), copy.clone()]
                .into_iter()
                .chain(copy_constraint);
            Constraints::with_selector(s_pub, constraints)
        });

        MerklePathConfig {
            value,
            public,
            copy_flag,
            index_flag,
            s_bucket: s_hash,
            s_pub,
            s_chash,
        }
    }

    /// Construct a [`Pow5Chip`].
    pub fn construct(config: MerklePathConfig<I>) -> Self {
        MerkleExtendedPathChip {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: PrimeField, const I: usize> MerkleExtendedPathInstruction<F, I>
    for MerkleExtendedPathChip<F, I>
{
    type Node = Node<F, I>;

    fn load_public_path(
        &self,
        layouter: &mut impl Layouter<F>,
        left: Vec<[AssignedCell<F, F>; I]>,
        right: Vec<[AssignedCell<F, F>; I]>,
        hash: Vec<[AssignedCell<F, F>; I]>,
        copy: &Vec<Value<F>>,
        len: usize,
        b: usize,
        position: usize,
    ) -> Result<(), Error> {
        let config = self.config();
        assert_eq!(len, right.len());
        assert_eq!(len, left.len());
        assert_eq!(len, copy.len());
        assert_eq!(len, hash.len());

        layouter.assign_region(
            || "load path",
            |mut region: Region<'_, F>| {
                // from first m-1 rows we do the hash copy check
                //
                // |  value  | copy | index| s_hash|
                // |  left1  |  *   |  *   |    0  |
                // |  right1 |  *   |  *   |    0  |
                // |  hash1  |  0   |  0   |    1  |
                // ....
                // hash(i) =  left(i+1) if index =0 else right(i+1)

                for i in 0..(len - 1) {
                    let cur_pos = i * 3;
                    let hash_pos = cur_pos + 2;
                    for j in 0..I {
                        left[i][j].copy_advice(
                            || "assign left",
                            &mut region,
                            config.value[j],
                            cur_pos,
                        )?;
                        right[i][j].copy_advice(
                            || "assign right",
                            &mut region,
                            config.value[j],
                            cur_pos + 1,
                        )?;
                        hash[i][j].copy_advice(
                            || "copy hash",
                            &mut region,
                            config.value[j],
                            hash_pos,
                        )?;
                    }

                    if i < (b - 1) {
                        // first b row, we use hash for sure
                        config.s_bucket.enable(&mut region, hash_pos)?;
                    } else {
                        config.s_chash.enable(&mut region, hash_pos)?;
                    }

                    region.assign_advice(
                        || "assign copy",
                        config.copy_flag,
                        hash_pos,
                        || copy[i],
                    )?;

                    region.assign_advice_from_instance(
                        || "assign index",
                        config.public,
                        position + i,
                        config.index_flag,
                        hash_pos,
                    )?;
                }

                // for the final row, we do not check index further but we do instance check

                let last_pos = (len - 1) * 3;
                for j in 0..I {
                    left[len - 1][j]
                        .copy_advice(|| "assign left", &mut region, config.value[j], last_pos)
                        .unwrap();
                    right[len - 1][j]
                        .copy_advice(
                            || "assign right",
                            &mut region,
                            config.value[j],
                            last_pos + 1,
                        )
                        .unwrap();
                }

                // assign next copy for the copy check
                region.assign_advice(
                    || "assign copy",
                    config.copy_flag,
                    last_pos + 2,
                    || Value::known(F::ZERO),
                )?;

                return Ok(());
            },
        )
    }

    fn expose_public(
        &self,
        layouter: &mut impl Layouter<F>,
        num: Self::Node,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();

        for i in 0..I {
            layouter.constrain_instance(num.0[i].cell(), config.public, row + i)?;
        }
        Ok(())
    }

    fn load_leaves(
        &self,
        layouter: &mut impl Layouter<F>,
        left: [AssignedCell<F, F>; I],
        right: [AssignedCell<F, F>; I],
        leaf_row: usize,
    ) -> Result<(), Error> {
        let config = self.config();

        layouter
            .assign_region(
                || "load inputs",
                |mut region: Region<'_, F>| {
                    // pub copy layer
                    // |  value  | copy | index|  s_pub|
                    // |  left   |  *   |   *  |    0  |
                    // |  right  |  *   |   *  |    0  |
                    // |  chosen |  0   |  0/1 |    1  |
                    // ....
                    // chosen = pub1,pub2, ... pubI

                    config.s_pub.enable(&mut region, 2)?;
                    for j in 0..I {
                        left[j].copy_advice(|| "assign left", &mut region, config.value[j], 0)?;
                        right[j].copy_advice(|| "assign right", &mut region, config.value[j], 1)?;
                        region.assign_advice_from_instance(
                            || "copy selected leaf from instance",
                            config.public,
                            leaf_row,
                            config.value[j],
                            2,
                        )?;
                    }

                    region.assign_advice_from_instance(
                        || "assign index for zero layer",
                        config.public,
                        leaf_row + 1,
                        config.index_flag,
                        2,
                    )?;

                    region.assign_advice(
                        || "assign copy",
                        config.copy_flag,
                        2,
                        || Value::known(F::ZERO),
                    )?;

                    Ok(())
                },
            )
            .unwrap();
        return Ok(());
    }
}

impl<F: PrimeField, const I: usize> Chip<F> for MerkleExtendedPathChip<F, I> {
    type Config = MerklePathConfig<I>;

    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
