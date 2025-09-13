mod constants;
mod evm;
mod pairings;
mod schemes;
mod withdraw;

use std::marker::PhantomData;

use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_groth16::Groth16;
use ark_r1cs_std::{
    fields::fp::FpVar,
    prelude::{AllocVar, EqGadget},
};
use ark_relations::r1cs::{ConstraintSynthesizer, SynthesisError};
use ark_snark::CircuitSpecificSetupSNARK;
use rand::thread_rng;

struct ExpCircuits<E: Pairing>(Option<u64>, Option<u64>, Option<u64>, PhantomData<E>);

pub trait PairingLibrary: Pairing {
    fn template(g2_addition: bool) -> String;

    fn g1_to_string(g1: &Self::G1Affine) -> String;

    fn g2_to_string(g2: &Self::G2Affine) -> String;
}

pub trait SolidityVerifier<E: PairingLibrary> {
    type Proof;
    type VerifyingKey;

    fn export(vk: &Self::VerifyingKey) -> String;
}

impl<E: Pairing> ConstraintSynthesizer<E::ScalarField> for ExpCircuits<E> {
    fn generate_constraints(
        self,
        cs: ark_relations::r1cs::ConstraintSystemRef<E::ScalarField>,
    ) -> ark_relations::r1cs::Result<()> {
        let base = FpVar::new_witness(cs.clone(), || {
            self.0
                .map(E::ScalarField::from)
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        let mult = FpVar::new_witness(cs.clone(), || {
            self.1
                .map(E::ScalarField::from)
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        let result = FpVar::new_input(cs.clone(), || {
            self.2
                .map(E::ScalarField::from)
                .ok_or(SynthesisError::AssignmentMissing)
        })?;

        (&base * &mult).enforce_equal(&result)?;

        Ok(())
    }
}

fn main() {
    let rng = &mut thread_rng();

    let (pk, vk) =
        Groth16::<Bn254>::setup(ExpCircuits::<Bn254>(None, None, None, PhantomData), rng).unwrap();
    let sol_verifier = Groth16::export(&vk);

    println!("{}", sol_verifier);
}
