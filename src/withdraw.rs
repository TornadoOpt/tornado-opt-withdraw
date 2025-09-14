// Cargo features expected (typical):
// ark-bn254, ark-groth16, ark-std, ark-crypto-primitives, ark-r1cs-std

use ark_bn254::Fr;
use ark_crypto_primitives::crh::{
    poseidon::constraints::{CRHParametersVar, TwoToOneCRHGadget},
    TwoToOneCRHSchemeGadget,
};
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    prelude::{AllocVar, CondSelectGadget},
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

/// Poseidon Merkle withdraw circuit (no folding, plain Groth16)
/// Public inputs:
///   - merkle_root : bytes32 as Fr
///   - nullifier_hash   : bytes32 as Fr
///   - recipient_f : Fr
///
/// Witness:
///   - nullifier, secret               (Fr)
///   - merkle_root       (Fr)
///   - path_siblings[H], path_bits[H]  (Fr / bool)
///   - recipient_square               (Fr)  -- recipient_f^2
///
/// Constraints:
///   1) nullifier_hash   == Poseidon2(TAG_NULL, nullifier)
///   2) leaf             == Poseidon2(Poseidon2(TAG_LEAF, nullifier), secret)
///   3) MerkleVerify_Poseidon2(merkle_root, leaf, siblings, bits)
///   4) recipient_f * recipient_f == recipient_square

#[derive(Clone)]
pub struct WithdrawCircuit<const H: usize> {
    // Poseidon parameters shared by leaf & internal nodes
    pub poseidon_params: PoseidonConfig<Fr>,

    // ---- public inputs ----
    pub merkle_root: Option<Fr>,
    pub nullifier_hash: Option<Fr>,
    pub recipient_f: Option<Fr>,

    // ---- witness ----
    pub nullifier: Option<Fr>,
    pub secret: Option<Fr>,
    pub path_siblings: [Option<Fr>; H],
    pub path_bits: [Option<bool>; H],
    pub recipient_square: Option<Fr>,
}

// Domain-separation tags (feel free to change to your canonical values)
const TAG_NULL: u64 = 12; // nullifier hash
const TAG_LEAF: u64 = 13; // leaf(commitment) = Poseidon2(Poseidon2(TAG_LEAF, nullifier), secret)

impl<const H: usize> ConstraintSynthesizer<Fr> for WithdrawCircuit<H> {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // ---- allocate public inputs ----
        let merkle_root_in = FpVar::<Fr>::new_input(cs.clone(), || {
            self.merkle_root.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let nullifier_hash_in = FpVar::<Fr>::new_input(cs.clone(), || {
            self.nullifier_hash.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let recipient_f_in = FpVar::<Fr>::new_input(cs.clone(), || {
            self.recipient_f.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // ---- allocate witnesses ----
        let nullifier = FpVar::<Fr>::new_witness(cs.clone(), || {
            self.nullifier.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let secret = FpVar::<Fr>::new_witness(cs.clone(), || {
            self.secret.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let recipient_square = FpVar::<Fr>::new_witness(cs.clone(), || {
            self.recipient_square
                .ok_or(SynthesisError::AssignmentMissing)
        })?;

        let params_var =
            CRHParametersVar::<Fr>::new_constant(cs.clone(), self.poseidon_params.clone())?;

        // siblings
        let mut siblings = Vec::with_capacity(H);
        for i in 0..H {
            siblings.push(FpVar::<Fr>::new_witness(cs.clone(), || {
                self.path_siblings[i].ok_or(SynthesisError::AssignmentMissing)
            })?);
        }
        // bits
        let mut bits = Vec::with_capacity(H);
        for i in 0..H {
            bits.push(Boolean::new_witness(cs.clone(), || {
                self.path_bits[i].ok_or(SynthesisError::AssignmentMissing)
            })?);
        }

        // ---- (1) nullifier hash check ----
        // nullifier_hash_calc = Poseidon2(TAG_NULL, nullifier)
        let tag_null = FpVar::<Fr>::constant(Fr::from(TAG_NULL));
        let nh_t = TwoToOneCRHGadget::<Fr>::evaluate(&params_var, &tag_null, &nullifier)?;
        nh_t.enforce_equal(&nullifier_hash_in)?;

        // ---- (2) leaf commitment ----
        // leaf = Poseidon2(Poseidon2(TAG_LEAF, nullifier), secret)
        let tag_leaf = FpVar::<Fr>::constant(Fr::from(TAG_LEAF));
        let t_leaf = TwoToOneCRHGadget::<Fr>::evaluate(&params_var, &tag_leaf, &nullifier)?;
        let leaf = TwoToOneCRHGadget::<Fr>::evaluate(&params_var, &t_leaf, &secret)?;

        // ---- (3) Merkle path verification (Poseidon 2→1) ----
        // node starts at leaf and is folded with siblings along path bits (LSB-first)
        let mut node = leaf;
        for lvl in 0..H {
            let b = &bits[lvl];
            let s = &siblings[lvl];
            let left = FpVar::<Fr>::conditionally_select(b, s, &node)?;
            let right = FpVar::<Fr>::conditionally_select(b, &node, s)?;
            node = TwoToOneCRHGadget::<Fr>::evaluate(&params_var, &left, &right)?;
        }
        node.enforce_equal(&merkle_root_in)?;

        // ---- (4) recipient binding (square) ----
        let r_sq = &recipient_f_in * &recipient_f_in;
        r_sq.enforce_equal(&recipient_square)?;

        Ok(())
    }
}

pub fn poseidon_canonical_config<F: PrimeField>() -> PoseidonConfig<F> {
    // 120 bit security target as in
    // https://eprint.iacr.org/2019/458.pdf
    // t = rate + 1

    let full_rounds = 8;
    let partial_rounds = 60;
    let alpha = 5;
    let rate = 4;

    let (ark, mds) = ark_crypto_primitives::sponge::poseidon::find_poseidon_ark_and_mds::<F>(
        F::MODULUS_BIT_SIZE as u64,
        rate,
        full_rounds,
        partial_rounds,
        0,
    );

    PoseidonConfig::new(
        full_rounds as usize,
        partial_rounds as usize,
        alpha,
        mds,
        ark,
        rate,
        1,
    )
}
#[cfg(test)]
mod tests {
    use std::io::Write as _;

    use super::*;
    use ark_bn254::Bn254;
    use ark_crypto_primitives::crh::{poseidon::TwoToOneCRH, TwoToOneCRHScheme as _};
    use ark_ff::{BigInteger as _, Field};
    use ark_groth16::Groth16;
    use ark_snark::{CircuitSpecificSetupSNARK, SNARK as _};
    use ark_std::UniformRand;
    use rand::{rngs::StdRng, SeedableRng as _};
    use sha3::{Digest, Keccak256};
    // If you have an exporter in your crate, re-enable:
    use crate::{
        evm::{compile_solidity, Evm},
        SolidityVerifier as _,
    };

    /// Native helper: Poseidon 2→1 compression using the same config as the circuit.
    fn h2(cfg: &PoseidonConfig<Fr>, a: Fr, b: Fr) -> Fr {
        TwoToOneCRH::<Fr>::evaluate(cfg, a, b).unwrap()
    }

    /// Build a Merkle root natively for sanity
    fn merkle_root_native<const H: usize>(
        cfg: &PoseidonConfig<Fr>,
        leaf: Fr,
        siblings: &[Fr; H],
        mut index: u64,
    ) -> Fr {
        let mut node = leaf;
        for i in 0..H {
            let bit = (index & 1) == 1;
            let (l, r) = if bit {
                (siblings[i], node)
            } else {
                (node, siblings[i])
            };
            node = h2(cfg, l, r);
            index >>= 1;
        }
        node
    }

    #[test]
    fn withdraw_circuit_groth16() {
        const H: usize = 20;

        // Poseidon config (Sonobe-aligned)
        let mut rng = StdRng::seed_from_u64(7);
        let poseidon_cfg: PoseidonConfig<Fr> = poseidon_canonical_config();
        // Random-ish data (deterministic RNG for test)
        let nullifier = Fr::rand(&mut rng);
        let secret = Fr::rand(&mut rng);
        let recipient_f = Fr::rand(&mut rng); // in production: field-encoding of 20-byte address

        // Tags
        let tag_null = Fr::from(super::TAG_NULL);
        let tag_leaf = Fr::from(super::TAG_LEAF);

        // nullifier_hash
        let nullifier_hash = h2(&poseidon_cfg, tag_null, nullifier);

        // leaf = Poseidon2(Poseidon2(TAG_LEAF, nullifier), secret)
        let t_leaf = h2(&poseidon_cfg, tag_leaf, nullifier);
        let leaf = h2(&poseidon_cfg, t_leaf, secret);

        // Merkle path (toy): all-zero siblings, index = 0
        let siblings: [Fr; H] = [Fr::from(0u64); H];
        let index_leaf: u64 = 0;
        let merkle_root = merkle_root_native::<H>(&poseidon_cfg, leaf, &siblings, index_leaf);

        // recipient_square
        let recipient_square = recipient_f.square();

        // Build circuit instance
        let circ = WithdrawCircuit::<H> {
            poseidon_params: poseidon_cfg.clone(),
            // public
            merkle_root: Some(merkle_root),
            nullifier_hash: Some(nullifier_hash),
            recipient_f: Some(recipient_f),
            // witness
            nullifier: Some(nullifier),
            secret: Some(secret),
            path_siblings: siblings.map(Some),
            path_bits: [false; H].map(Some),
            recipient_square: Some(recipient_square),
        };

        // Prove & verify (Groth16 over BN254)
        let mut rng = StdRng::seed_from_u64(7);
        let (pk, vk) = Groth16::<Bn254>::setup(circ.clone(), &mut rng).unwrap();
        let proof: ark_groth16::Proof<ark_ec::bn::Bn<ark_bn254::Config>> =
            Groth16::<Bn254>::prove(&pk, circ, &mut rng).unwrap();

        // Public inputs order must match allocation order
        let publics = [merkle_root, nullifier_hash, recipient_f];

        assert!(Groth16::<Bn254>::verify(&vk, &publics, &proof).unwrap());

        // If you have an on-chain exporter, re-enable:
        let sol_verifier = Groth16::export(&vk);
        println!("{}", sol_verifier);

        // If you have an on-chain exporter, re-enable:
        let sol_verifier = Groth16::export(&vk);
        // save to file for debugging
        {
            let mut f = std::fs::File::create("withdraw_solidity_verifier.sol").unwrap();
            f.write_all(sol_verifier.as_bytes()).unwrap();
        }

        let verifier_bytecode = compile_solidity(&sol_verifier, "Verifier");
        let mut evm = Evm::default();
        let verifier_address = evm.create(verifier_bytecode);

        fn fe_to_be_bytes<F: ark_ff::PrimeField>(f: &F) -> [u8; 32] {
            let mut out = [0u8; 32];
            let bytes = f.into_bigint().to_bytes_be();
            let start = 32 - bytes.len();
            out[start..].copy_from_slice(&bytes);
            out
        }

        // Calldata for public wrapper verifyTx(Proof,uint256[N]) to actually run on EVM
        let sig_tx = format!(
            "verifyTx(((uint256,uint256),(uint256[2],uint256[2]),(uint256,uint256)),uint256[{}])",
            publics.len()
        );
        let mut h_tx = Keccak256::new();
        h_tx.update(sig_tx.as_bytes());
        let selector_tx = &h_tx.finalize()[..4];
        let mut calldata_verify_tx = Vec::with_capacity(4 + (8 + publics.len()) * 32);
        calldata_verify_tx.extend_from_slice(selector_tx);
        // proof (static)
        calldata_verify_tx.extend_from_slice(&fe_to_be_bytes(&proof.a.x));
        calldata_verify_tx.extend_from_slice(&fe_to_be_bytes(&proof.a.y));
        calldata_verify_tx.extend_from_slice(&fe_to_be_bytes(&proof.b.x.c0));
        calldata_verify_tx.extend_from_slice(&fe_to_be_bytes(&proof.b.x.c1));
        calldata_verify_tx.extend_from_slice(&fe_to_be_bytes(&proof.b.y.c0));
        calldata_verify_tx.extend_from_slice(&fe_to_be_bytes(&proof.b.y.c1));
        calldata_verify_tx.extend_from_slice(&fe_to_be_bytes(&proof.c.x));
        calldata_verify_tx.extend_from_slice(&fe_to_be_bytes(&proof.c.y));
        // fixed-size uint[N]
        for pi in publics.iter() {
            calldata_verify_tx.extend_from_slice(&fe_to_be_bytes(pi));
        }

        let (_, output) = evm.call(verifier_address, calldata_verify_tx.clone());
        assert_eq!(*output.last().unwrap(), 1);
    }
}
