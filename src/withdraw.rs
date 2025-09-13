// Cargo features expected (typical):
// ark-bn254, ark-groth16, ark-std, ark-crypto-primitives, ark-r1cs-std

use ark_bn254::{Bn254, Fr};
use ark_crypto_primitives::crh::TwoToOneCRHScheme;
use ark_crypto_primitives::crh::{
    poseidon::{
        constraints::{CRHParametersVar, TwoToOneCRHGadget},
        TwoToOneCRH,
    },
    TwoToOneCRHSchemeGadget,
};
use ark_crypto_primitives::sponge::poseidon::{find_poseidon_ark_and_mds, PoseidonConfig};
use ark_ff::PrimeField;
use ark_groth16::Groth16;
use ark_r1cs_std::{
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    prelude::{AllocVar, CondSelectGadget},
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_snark::SNARK;
use ark_std::rand::{rngs::StdRng, SeedableRng};

/// Poseidon Merkle withdraw circuit (no folding, plain Groth16)
/// Public inputs:
///   - state_commitment : bytes32 as Fr
///   - nullifier_hash   : bytes32 as Fr
///   - recipient_square : Fr    (recipient_f^2 mod p)
///
/// Witness:
///   - nullifier, secret               (Fr)
///   - merkle_root, index_upper        (Fr)  -- used only to "open" state_commitment
///   - path_siblings[H], path_bits[H]  (Fr / bool)
///   - recipient_f                     (Fr)  -- field-encoded recipient (20B -> int -> Fr)
///
/// Constraints:
///   1) state_commitment == Poseidon2(Poseidon2(TAG_CP, merkle_root), index_upper)
///   2) nullifier_hash   == Poseidon2(TAG_NULL, nullifier)
///   3) leaf             == Poseidon2(Poseidon2(TAG_LEAF, nullifier), secret)
///   4) MerkleVerify_Poseidon2(merkle_root, leaf, siblings, bits)
///   5) recipient_f * recipient_f == recipient_square
#[derive(Clone)]
pub struct WithdrawCircuit<const H: usize> {
    // Poseidon parameters shared by leaf & internal nodes
    pub poseidon_params: PoseidonConfig<Fr>,

    // ---- public inputs ----
    pub state_commitment: Option<Fr>,
    pub nullifier_hash: Option<Fr>,
    pub recipient_square: Option<Fr>,

    // ---- witness ----
    pub nullifier: Option<Fr>,
    pub secret: Option<Fr>,
    pub merkle_root: Option<Fr>,
    pub index_upper: Option<Fr>,
    pub path_siblings: [Option<Fr>; H],
    pub path_bits: [Option<bool>; H],
    pub recipient_f: Option<Fr>,
}

// Domain-separation tags (feel free to change to your canonical values)
const TAG_CP: u64 = 11; // commitment to (merkle_root, index_upper)
const TAG_NULL: u64 = 12; // nullifier hash
const TAG_LEAF: u64 = 13; // leaf(commitment) = Poseidon2(Poseidon2(TAG_LEAF, nullifier), secret)

impl<const H: usize> ConstraintSynthesizer<Fr> for WithdrawCircuit<H> {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // ---- allocate public inputs ----
        let state_commitment_in = FpVar::<Fr>::new_input(cs.clone(), || {
            self.state_commitment
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        let nullifier_hash_in = FpVar::<Fr>::new_input(cs.clone(), || {
            self.nullifier_hash.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let recipient_square_in = FpVar::<Fr>::new_input(cs.clone(), || {
            self.recipient_square
                .ok_or(SynthesisError::AssignmentMissing)
        })?;

        // ---- allocate witnesses ----
        let nullifier = FpVar::<Fr>::new_witness(cs.clone(), || {
            self.nullifier.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let secret = FpVar::<Fr>::new_witness(cs.clone(), || {
            self.secret.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let merkle_root = FpVar::<Fr>::new_witness(cs.clone(), || {
            self.merkle_root.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let index_upper = FpVar::<Fr>::new_witness(cs.clone(), || {
            self.index_upper.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let recipient_f = FpVar::<Fr>::new_witness(cs.clone(), || {
            self.recipient_f.ok_or(SynthesisError::AssignmentMissing)
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

        // ---- (2) nullifier hash check ----
        // nullifier_hash_calc = Poseidon2(TAG_NULL, nullifier)
        let tag_null = FpVar::<Fr>::constant(Fr::from(TAG_NULL));
        let nh_t = TwoToOneCRHGadget::<Fr>::evaluate(&params_var, &tag_null, &nullifier)?;
        nh_t.enforce_equal(&nullifier_hash_in)?;

        // ---- (3) leaf commitment ----
        // leaf = Poseidon2(Poseidon2(TAG_LEAF, nullifier), secret)
        let tag_leaf = FpVar::<Fr>::constant(Fr::from(TAG_LEAF));
        let t_leaf = TwoToOneCRHGadget::<Fr>::evaluate(&params_var, &tag_leaf, &nullifier)?;
        let leaf = TwoToOneCRHGadget::<Fr>::evaluate(&params_var, &t_leaf, &secret)?;

        // ---- (4) Merkle path verification (Poseidon 2→1) ----
        // node starts at leaf and is folded with siblings along path bits (LSB-first)
        let mut node = leaf;
        for lvl in 0..H {
            let b = &bits[lvl];
            let s = &siblings[lvl];
            let left = FpVar::<Fr>::conditionally_select(b, s, &node)?;
            let right = FpVar::<Fr>::conditionally_select(b, &node, s)?;
            node = TwoToOneCRHGadget::<Fr>::evaluate(&params_var, &left, &right)?;
        }
        node.enforce_equal(&merkle_root)?;

        // ---- (1) state_commitment open ----
        // sc = Poseidon2(Poseidon2(TAG_CP, merkle_root), index_upper)
        let tag_cp = FpVar::<Fr>::constant(Fr::from(TAG_CP));
        let t_cp = TwoToOneCRHGadget::<Fr>::evaluate(&params_var, &tag_cp, &merkle_root)?;
        let sc = TwoToOneCRHGadget::<Fr>::evaluate(&params_var, &t_cp, &index_upper)?;
        sc.enforce_equal(&state_commitment_in)?;

        // ---- (5) recipient binding (square) ----
        let r_sq = &recipient_f * &recipient_f;
        r_sq.enforce_equal(&recipient_square_in)?;

        Ok(())
    }
}

/// Sonobe transcript-aligned Poseidon config for BN254 (used for 2→1 Merkle compression / CRH):
///   rate=2, capacity=1 (width=3), alpha=5, full_rounds=8, partial_rounds=56.
/// MDS/ARK are derived via `find_poseidon_ark_and_mds` exactly like Sonobe.
fn sonobe_poseidon2to1_cfg() -> PoseidonConfig<Fr> {
    let rate = 2usize;
    let capacity = 1usize;
    let full_rounds = 8usize;
    let partial_rounds = 56usize;

    let (ark, mds) = find_poseidon_ark_and_mds::<Fr>(
        Fr::MODULUS_BIT_SIZE as u64,
        rate,
        full_rounds as u64,
        partial_rounds as u64,
        0, // seed index
    );
    PoseidonConfig::new(full_rounds, partial_rounds, 5u64, mds, ark, rate, capacity)
}

// --------------------------- a tiny self-check test ---------------------------

#[cfg(test)]
mod tests {
    use std::io::Write as _;

    use super::*;
    use crate::{
        evm::{compile_solidity, Evm},
        SolidityVerifier,
    };
    use ark_ff::{BigInteger as _, Field};
    use ark_snark::CircuitSpecificSetupSNARK;
    use ark_std::UniformRand;
    use sha3::{Digest, Keccak256};

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
        let mut rng = StdRng::seed_from_u64(42);
        let poseidon_cfg: PoseidonConfig<Fr> = super::sonobe_poseidon2to1_cfg();

        // Random-ish data (deterministic RNG for test)
        let nullifier = Fr::rand(&mut rng);
        let secret = Fr::rand(&mut rng);
        let recipient_f = Fr::rand(&mut rng); // in production: field-encoding of 20-byte address

        // Tags
        let tag_cp = Fr::from(super::TAG_CP);
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

        // state_commitment = Poseidon2(Poseidon2(TAG_CP, merkle_root), index_upper)
        let index_upper = Fr::from(123u64); // any policy you like
        let t_cp = h2(&poseidon_cfg, tag_cp, merkle_root);
        let state_commitment = h2(&poseidon_cfg, t_cp, index_upper);

        // recipient_square
        let recipient_square = recipient_f.square();

        // Build circuit instance
        let circ = WithdrawCircuit::<H> {
            poseidon_params: poseidon_cfg.clone(),
            // public
            state_commitment: Some(state_commitment),
            nullifier_hash: Some(nullifier_hash),
            recipient_square: Some(recipient_square),
            // witness
            nullifier: Some(nullifier),
            secret: Some(secret),
            merkle_root: Some(merkle_root),
            index_upper: Some(index_upper),
            path_siblings: siblings.map(Some),
            path_bits: [false; H].map(Some),
            recipient_f: Some(recipient_f),
        };

        // Prove & verify (Groth16 over BN254)
        let mut rng = StdRng::seed_from_u64(7);
        let (pk, vk) = Groth16::<Bn254>::setup(circ.clone(), &mut rng).unwrap();
        let proof = Groth16::<Bn254>::prove(&pk, circ, &mut rng).unwrap();

        // Public inputs order must match allocation order
        let publics = [state_commitment, nullifier_hash, recipient_square];

        assert!(Groth16::<Bn254>::verify(&vk, &publics, &proof).unwrap());

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
