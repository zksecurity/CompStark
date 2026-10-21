//! Known answers over BabyBear: Plonky3's default Poseidon2 permutations, its Poseidon2 Merkle
//! hashes, the width-24 duplex challenger, and `uni-stark` proofs with the configuration of
//! `stark.rs` over BabyBear.
use p3_baby_bear::{
    default_babybear_poseidon2_16, default_babybear_poseidon2_24, BabyBear as F,
    Poseidon2BabyBear,
};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, Permutation, TruncatedPermutation};
use p3_uni_stark::{prove, verify, StarkConfig};

use crate::stark::{cube_trace, trace, CubeAir, FibonacciAir};

type Perm16 = Poseidon2BabyBear<16>;
type Perm24 = Poseidon2BabyBear<24>;
type Hash = PaddingFreeSponge<Perm24, 24, 16, 8>;
type Compress = TruncatedPermutation<Perm16, 2, 8, 16>;
type ValMmcs = MerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing, Hash, Compress, 8>;
type Challenge = BinomialExtensionField<F, 4>;
type ChallengeMmcs = ExtensionMmcs<F, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<F, Perm24, 24, 16>;
type Pcs = TwoAdicFriPcs<F, Radix2DitParallel<F>, ValMmcs, ChallengeMmcs>;
type Config = StarkConfig<Pcs, Challenge, Challenger>;

fn show<const W: usize>(label: &str, input: [u32; W], perm: &impl Permutation<[F; W]>) {
    let mut state = input.map(F::from_u32);
    perm.permute_mut(&mut state);
    let out: Vec<u32> = state.iter().map(|x| x.as_canonical_u32()).collect();
    println!("{label} {:?}\n  -> {:?}", input, out);
}

/// `babybear`: the permutations on fixed inputs, the sponge and compression, and the challenger
/// sequence of `stark::challenger`, as canonical values. Run with `RAYON_NUM_THREADS=1`.
pub fn known_answers() {
    use p3_challenger::{CanObserve, CanSample, CanSampleBits, FieldChallenger, GrindingChallenger};
    use p3_field::BasedVectorSpace;
    use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};
    let p16 = default_babybear_poseidon2_16();
    let p24 = default_babybear_poseidon2_24();
    show("w16 zero", [0u32; 16], &p16);
    show("w16 iota", core::array::from_fn::<u32, 16, _>(|i| i as u32), &p16);
    show("w16 sage", [894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695,
        1717947831, 120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443,
        227047920, 1783754913], &p16);
    show("w24 zero", [0u32; 24], &p24);
    show("w24 iota", core::array::from_fn::<u32, 24, _>(|i| i as u32), &p24);
    let hash = Hash::new(p24.clone());
    let compress = Compress::new(p16.clone());
    for n in [0u32, 17, 50] {
        let out: [F; 8] = hash.hash_iter((0..n).map(F::from_u32));
        let out: Vec<u32> = out.iter().map(|x| x.as_canonical_u32()).collect();
        println!("sponge iota {n} -> {:?}", out);
    }
    let a: [F; 8] = core::array::from_fn(|i| F::from_u32(i as u32));
    let b: [F; 8] = core::array::from_fn(|i| F::from_u32(100 + i as u32));
    let out: Vec<u32> = compress.compress([a, b]).iter().map(|x| x.as_canonical_u32()).collect();
    println!("compress iota/100 -> {:?}", out);
    let mut c = Challenger::new(p24);
    for i in 0..20u32 {
        c.observe(F::from_u32(i));
    }
    let a: F = c.sample();
    let b: F = c.sample();
    let e: Challenge = c.sample_algebra_element();
    c.observe(F::from_u32(7));
    c.observe_algebra_element(Challenge::from_basis_coefficients_fn(|i| F::from_u32(100 + i as u32)));
    let bits = c.sample_bits(10);
    let w = c.grind(6);
    let z: F = c.sample();
    let ext: Vec<u32> = BasedVectorSpace::<F>::as_basis_coefficients_slice(&e).iter()
        .map(|x| x.as_canonical_u32()).collect();
    println!("challenger {} {} {:?} {} {} {}", a.as_canonical_u32(), b.as_canonical_u32(), ext,
        bits, w.as_canonical_u32(), z.as_canonical_u32());
}

/// `stark-babybear AIR LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW`, `AIR`
/// one of `fib`, `cube`: the proof over BabyBear as JSON, after Plonky3 verified it. Run with
/// `RAYON_NUM_THREADS=1` for the smallest grinding witnesses.
pub fn stark(air: &str, args: &[usize]) {
    let [log_n, log_blowup, log_final_poly_len, max_log_arity, num_queries, commit_pow, query_pow] =
        args[..]
    else {
        panic!("usage: stark-babybear AIR LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW")
    };
    let hash = Hash::new(default_babybear_poseidon2_24());
    let compress = Compress::new(default_babybear_poseidon2_16());
    let val_mmcs = ValMmcs::new(hash, compress);
    let fri = FriParameters {
        log_blowup,
        log_final_poly_len,
        max_log_arity,
        num_queries,
        commit_proof_of_work_bits: commit_pow,
        query_proof_of_work_bits: query_pow,
        mmcs: ChallengeMmcs::new(val_mmcs.clone()),
    };
    let pcs = Pcs::new(Radix2DitParallel::default(), val_mmcs, fri);
    let config = Config::new(pcs, Challenger::new(default_babybear_poseidon2_24()));
    let proof = match air {
        "fib" => {
            let (trace, x) = trace::<F>(1 << log_n);
            let pis = vec![F::ZERO, F::ONE, x];
            let proof = prove(&config, &FibonacciAir, trace, &pis);
            verify(&config, &FibonacciAir, &proof, &pis).expect("Plonky3 rejects its own proof");
            proof
        }
        "cube" => {
            let (trace, x) = cube_trace::<F>(1 << log_n);
            let pis = vec![F::TWO, F::ZERO, x];
            let proof = prove(&config, &CubeAir, trace, &pis);
            verify(&config, &CubeAir, &proof, &pis).expect("Plonky3 rejects its own proof");
            proof
        }
        _ => panic!("unknown AIR {air}"),
    };
    println!("{}", serde_json::to_string(&proof).unwrap());
}
