use halo2_proofs::{
    pasta::EqAffine,
    plonk::{ProvingKey, VerifyingKey},
    poly::commitment::Params,
};

use crate::proof::{EHProof, Proof};

pub trait SetCommitment<const LE: usize, const LM: usize, const LB: usize> {
    type Element;

    fn prove(&self, element: &Self::Element) -> Proof<LE, LB>;

    fn verify_membership(
        element: &Self::Element,
        proof: &Proof<LE, LB>,
        set_commitment: &[u8; 32],
        k: u32,
    ) -> Result<bool, String>;
}

pub trait EHScheme<const LE: usize, const LM: usize, const LB: usize> {
    type Element;

    fn eh_prove_halo(
        &self,
        element: &Self::Element,
        param: &Params<EqAffine>,
        pk: &ProvingKey<EqAffine>,
    ) -> EHProof<LE, LM, LB>;

    fn eh_verify_halo(
        proof: &EHProof<LE, LM, LB>,
        set_commitment: &[u8; 32],
        k: u32,
        param: &Params<EqAffine>,
        vk: &VerifyingKey<EqAffine>,
    ) -> Result<bool, String>;

    fn eh_setup() -> (Params<EqAffine>, ProvingKey<EqAffine>);
}
