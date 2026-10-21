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

/// Two columns `x, y`: rows `(a, b)` first, `(x³ + y, y + 1)` next, and `x = c` last. Its
/// transition constraint has degree 3 (the transition selector counts as degree 0), so the
/// quotient has two chunks.
pub struct CubeAir;

impl<T> BaseAir<T> for CubeAir {
    fn width(&self) -> usize {
        2
    }
}

impl<AB: AirBuilderWithPublicValues> Air<AB> for CubeAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let pis = builder.public_values();
        let (a, b, c) = (pis[0], pis[1], pis[2]);
        let local = main.row_slice(0).unwrap();
        let next = main.row_slice(1).unwrap();
        let local: &[AB::Var] = (*local).borrow();
        let next: &[AB::Var] = (*next).borrow();
        let mut first = builder.when_first_row();
        first.assert_eq(local[0].clone(), a);
        first.assert_eq(local[1].clone(), b);
        let x: AB::Expr = local[0].clone().into();
        let mut transition = builder.when_transition();
        transition.assert_eq(x.clone() * x.clone() * x + local[1].clone(), next[0].clone());
        transition.assert_eq(local[1].clone() + AB::Expr::ONE, next[1].clone());
        builder.when_last_row().assert_eq(local[0].clone(), c);
    }
}

/// The trace of `n` rows of `CubeAir` from `(2, 0)`, and its last `x`.
pub fn cube_trace<F: Field>(n: usize) -> (RowMajorMatrix<F>, F) {
    let mut values = Vec::with_capacity(2 * n);
    let (mut x, mut y) = (F::TWO, F::ZERO);
    for _ in 0..n {
        values.push(x);
        values.push(y);
        (x, y) = (x * x * x + y, y + F::ONE);
    }
    let last = values[2 * n - 2];
    (RowMajorMatrix::new(values, 2), last)
}

/// The width of `WideAir`.
pub const WIDE: usize = 64;

/// `WIDE` columns, each next row `x'ⱼ = xⱼ³ + xⱼ₊₁` (indices mod `WIDE`): a representative wide
/// trace with degree-3 transitions and a two-chunk quotient, no public values.
pub struct WideAir;

impl<T> BaseAir<T> for WideAir {
    fn width(&self) -> usize {
        WIDE
    }
}

impl<AB: AirBuilderWithPublicValues> Air<AB> for WideAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let next = main.row_slice(1).unwrap();
        let local: &[AB::Var] = (*local).borrow();
        let next: &[AB::Var] = (*next).borrow();
        let mut transition = builder.when_transition();
        for j in 0..WIDE {
            let x: AB::Expr = local[j].clone().into();
            transition.assert_eq(x.clone() * x.clone() * x + local[(j + 1) % WIDE].clone(),
                next[j].clone());
        }
    }
}

/// The trace of `n` rows of `WideAir` from `xⱼ = j`.
fn wide_trace(n: usize) -> RowMajorMatrix<F> {
    let mut values = Vec::with_capacity(WIDE * n);
    let mut row: Vec<F> = (0..WIDE).map(|j| F::from_u32(j as u32)).collect();
    for _ in 0..n {
        values.extend_from_slice(&row);
        row = (0..WIDE).map(|j| row[j] * row[j] * row[j] + row[(j + 1) % WIDE]).collect();
    }
    RowMajorMatrix::new(values, WIDE)
}

/// The trace of `n` Fibonacci rows from `(0, 1)`, and its last right value.
pub fn trace<F: Field>(n: usize) -> (RowMajorMatrix<F>, F) {
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

/// `stark AIR LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW`, `AIR` one
/// of `fib`, `cube`: the proof as JSON, after Plonky3 verified it. Run with
/// `RAYON_NUM_THREADS=1` for the smallest grinding witnesses.
pub fn stark(air: &str, args: &[usize]) {
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
    let proof = match air {
        "fib" => {
            let (trace, x) = trace(1 << log_n);
            let pis = vec![F::ZERO, F::ONE, x];
            let proof = prove(&config, &FibonacciAir, trace, &pis);
            verify(&config, &FibonacciAir, &proof, &pis).expect("Plonky3 rejects its own proof");
            proof
        }
        "cube" => {
            let (trace, x) = cube_trace(1 << log_n);
            let pis = vec![F::TWO, F::ZERO, x];
            let proof = prove(&config, &CubeAir, trace, &pis);
            verify(&config, &CubeAir, &proof, &pis).expect("Plonky3 rejects its own proof");
            proof
        }
        "wide" => {
            let trace = wide_trace(1 << log_n);
            let proof = prove(&config, &WideAir, trace, &[]);
            verify(&config, &WideAir, &proof, &[]).expect("Plonky3 rejects its own proof");
            proof
        }
        _ => panic!("unknown AIR {air}"),
    };
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

/// `prove-bench AIR LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW`: the
/// median milliseconds of seven proofs.
pub fn prove_bench(air: &str, args: &[usize]) {
    use std::time::Instant;
    let [log_n, log_blowup, log_final_poly_len, max_log_arity, num_queries, commit_pow, query_pow] =
        args[..]
    else {
        panic!("seven parameters")
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
    let mut samples = vec![];
    for _ in 0..7 {
        let (trace, pis) = match air {
            "fib" => { let (t, x) = trace(1 << log_n); (t, vec![F::ZERO, F::ONE, x]) }
            "cube" => { let (t, x) = cube_trace(1 << log_n); (t, vec![F::TWO, F::ZERO, x]) }
            "wide" => (wide_trace(1 << log_n), vec![]),
            _ => panic!("unknown AIR {air}"),
        };
        let t = Instant::now();
        let proof = match air {
            "fib" => prove(&config, &FibonacciAir, trace, &pis),
            "wide" => prove(&config, &WideAir, trace, &pis),
            _ => prove(&config, &CubeAir, trace, &pis),
        };
        samples.push(t.elapsed().as_secs_f64() * 1000.0);
        std::hint::black_box(proof);
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("plonky3 prove {air} 2^{log_n} ms median {:.2}", samples[3]);
}

/// `prove-trace AIR LOG_N …`: one proof with Plonky3's tracing spans printed.
pub fn prove_trace(air: &str, args: &[usize]) {
    use tracing_forest::util::LevelFilter;
    use tracing_forest::ForestLayer;
    use tracing_subscriber::layer::SubscriberExt;
    use tracing_subscriber::util::SubscriberInitExt;
    use tracing_subscriber::{EnvFilter, Registry};
    let env_filter = EnvFilter::builder().with_default_directive(LevelFilter::INFO.into()).from_env_lossy();
    Registry::default().with(env_filter).with(ForestLayer::default()).init();
    prove_bench(air, args);
}
