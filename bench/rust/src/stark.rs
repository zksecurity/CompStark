//! Plonky3 `uni-stark` proofs over KoalaBear for known-answer tests: the Poseidon2 Merkle
//! commitment of `examples/src/types.rs`, a width-24 duplex challenger, and a Fibonacci AIR.
use core::borrow::Borrow;
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_koala_bear::{
    default_koalabear_poseidon2_16, default_koalabear_poseidon2_24, KoalaBear as F,
    Poseidon2KoalaBear,
};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, StarkConfig};

type Perm16 = Poseidon2KoalaBear<16>;
type Perm24 = Poseidon2KoalaBear<24>;
type Hash = PaddingFreeSponge<Perm24, 24, 16, 8>;
type Compress = TruncatedPermutation<Perm16, 2, 8, 16>;
type ValMmcs = MerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing, Hash, Compress, 8>;
type Challenge = BinomialExtensionField<F, 4>;
type ChallengeMmcs = ExtensionMmcs<F, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<F, Perm24, 24, 16>;
type Pcs = TwoAdicFriPcs<F, Radix2DitParallel<F>, ValMmcs, ChallengeMmcs>;
type Config = StarkConfig<Pcs, Challenge, Challenger>;

/// Two columns `left, right`: rows `(a, b)` first, `(right, left + right)` next, and `right = x` last.
pub struct FibonacciAir;

impl<T> BaseAir<T> for FibonacciAir {
    fn width(&self) -> usize {
        2
    }
}

impl<AB: AirBuilderWithPublicValues> Air<AB> for FibonacciAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let pis = builder.public_values();
        let (a, b, x) = (pis[0], pis[1], pis[2]);
        let local = main.row_slice(0).unwrap();
        let next = main.row_slice(1).unwrap();
        let local: &[AB::Var] = (*local).borrow();
        let next: &[AB::Var] = (*next).borrow();
        let mut first = builder.when_first_row();
        first.assert_eq(local[0].clone(), a);
        first.assert_eq(local[1].clone(), b);
        let mut transition = builder.when_transition();
        transition.assert_eq(local[1].clone(), next[0].clone());
        transition.assert_eq(local[0].clone() + local[1].clone(), next[1].clone());
        builder.when_last_row().assert_eq(local[1].clone(), x);
    }
}

/// The trace of `n` Fibonacci rows from `(0, 1)`, and its last right value.
fn trace(n: usize) -> (RowMajorMatrix<F>, F) {
    let mut values = Vec::with_capacity(2 * n);
    let (mut l, mut r) = (F::ZERO, F::ONE);
    for _ in 0..n {
        values.push(l);
        values.push(r);
        (l, r) = (r, l + r);
    }
    let last = values[2 * n - 1];
    (RowMajorMatrix::new(values, 2), last)
}

/// `stark LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW`: the proof as
/// JSON, after Plonky3 verified it. Run with `RAYON_NUM_THREADS=1` for the smallest grinding
/// witnesses.
pub fn stark(args: &[usize]) {
    let [log_n, log_blowup, log_final_poly_len, max_log_arity, num_queries, commit_pow, query_pow] =
        args[..]
    else {
        panic!("usage: stark LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW")
    };
    let hash = Hash::new(default_koalabear_poseidon2_24());
    let compress = Compress::new(default_koalabear_poseidon2_16());
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
    let config = Config::new(pcs, Challenger::new(default_koalabear_poseidon2_24()));
    let (trace, x) = trace(1 << log_n);
    assert!(trace.height() == 1 << log_n);
    let pis = vec![F::ZERO, F::ONE, x];
    let proof = prove(&config, &FibonacciAir, trace, &pis);
    verify(&config, &FibonacciAir, &proof, &pis).expect("Plonky3 rejects its own proof");
    println!("{}", serde_json::to_string(&proof).unwrap());
}

/// A fixed sequence on the STARK challenger: observe `0, …, 19`, sample two base elements and an
/// extension element, observe `7` and an extension element, sample 10 bits, grind 6 bits, and
/// sample once more. Canonical values. Run with `RAYON_NUM_THREADS=1`.
pub fn challenger() {
    use p3_challenger::{CanObserve, CanSample, CanSampleBits, FieldChallenger, GrindingChallenger};
    use p3_field::{BasedVectorSpace, PrimeField32};
    let mut c = Challenger::new(default_koalabear_poseidon2_24());
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
    let ext: Vec<u32> = BasedVectorSpace::<F>::as_basis_coefficients_slice(&e).iter().map(|x| x.as_canonical_u32()).collect();
    println!("challenger {} {} {:?} {} {} {}", a.as_canonical_u32(), b.as_canonical_u32(), ext, bits,
        w.as_canonical_u32(), z.as_canonical_u32());
}
