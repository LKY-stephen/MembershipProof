use ff::Field;
use halo2_proofs::pasta::Fp;

use halo2_gadgets::poseidon::primitives::{generate_constants, Mds, Spec};

#[derive(Debug, Clone, Copy)]
pub(crate) struct PoseidonSpec<const W: usize, const R: usize>;

impl<const W: usize, const R: usize> Spec<Fp, W, R> for PoseidonSpec<W, R> {
    fn full_rounds() -> usize {
        8
    }

    fn partial_rounds() -> usize {
        56
    }

    fn sbox(val: Fp) -> Fp {
        val.pow_vartime(&[5])
    }

    fn secure_mds() -> usize {
        0
    }

    fn constants() -> (Vec<[Fp; W]>, Mds<Fp, W>, Mds<Fp, W>) {
        generate_constants::<_, Self, W, R>()
    }
}
