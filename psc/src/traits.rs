use halo2_proofs::{
    pasta::EqAffine,
    plonk::{ProvingKey, VerifyingKey},
    poly::commitment::Params,
};

use crate::proof::{EHProof, Proof, SHProof};

pub trait SetCommitment<const LE: usize, const LM: usize, const LB: usize> {
    type Element;

    fn prove(&self, element: &Self::Element) -> Proof<LE, LB>;

    fn verify_membership(
        element: &Self::Element,
        proof: &Proof<LE, LB>,
        set_commitment: &[u8; 32],
        k_commitment: &[u64; 4],
    ) -> Result<bool, String>;
}

pub trait SHScheme<const LE: usize, const LM: usize, const LB: usize> {
    type Element;

    fn sh_prove_halo(
        &self,
        element: &Self::Element,
        param: &Params<EqAffine>,
        pk: &ProvingKey<EqAffine>,
    ) -> SHProof<LE, LM, LB>;

    fn sh_verify_halo(
        element: &Self::Element,
        proof: &SHProof<LE, LM, LB>,
        set_commitment: &[u8; 32],
        k_commitment: &[u64; 4],
        param: &Params<EqAffine>,
        vk: &VerifyingKey<EqAffine>,
    ) -> Result<bool, String>;

    fn sh_setup() -> (Params<EqAffine>, ProvingKey<EqAffine>);
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
        k_commitment: &[u64; 4],
        param: &Params<EqAffine>,
        vk: &VerifyingKey<EqAffine>,
    ) -> Result<bool, String>;

    fn eh_setup() -> (Params<EqAffine>, ProvingKey<EqAffine>);
}
