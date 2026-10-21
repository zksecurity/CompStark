//! Plonky3 `uni-stark` proofs for known-answer tests: the Poseidon2 Merkle commitment of
//! `examples/src/types.rs` (binary, cap height 0), a width-24 duplex challenger, and AIRs with
//! preprocessed and periodic columns.
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::extension::BinomiallyExtendable;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_koala_bear::{
    default_koalabear_poseidon2_16, default_koalabear_poseidon2_24, KoalaBear,
};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{CryptographicPermutation, PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{
    prove, prove_with_preprocessed, setup_preprocessed, verify, verify_with_preprocessed, Proof,
    StarkConfig,
};

type F = KoalaBear;

pub type Hash<P24> = PaddingFreeSponge<P24, 24, 16, 8>;
pub type Compress<P16> = TruncatedPermutation<P16, 2, 8, 16>;
pub type ValMmcs<F, P16, P24> =
    MerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing, Hash<P24>, Compress<P16>, 2, 8>;
pub type Challenge<F> = BinomialExtensionField<F, 4>;
pub type ChallengeMmcs<F, P16, P24> = ExtensionMmcs<F, Challenge<F>, ValMmcs<F, P16, P24>>;
pub type Challenger<F, P24> = DuplexChallenger<F, P24, 24, 16>;
pub type Pcs<F, P16, P24> =
    TwoAdicFriPcs<F, Radix2DitParallel<F>, ValMmcs<F, P16, P24>, ChallengeMmcs<F, P16, P24>>;
pub type Config<F, P16, P24> = StarkConfig<Pcs<F, P16, P24>, Challenge<F>, Challenger<F, P24>>;

/// The configuration from the parameters `LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW
/// QUERY_POW [BATCH_POW OOD_POW]` (the last two default to 0).
pub fn config<F, P16, P24>(p16: P16, p24: P24, args: &[usize]) -> Config<F, P16, P24>
where
    F: TwoAdicField + PrimeField64 + BinomiallyExtendable<4>,
    P16: CryptographicPermutation<[F; 16]> + CryptographicPermutation<[F::Packing; 16]>,
    P24: CryptographicPermutation<[F; 24]> + CryptographicPermutation<[F::Packing; 24]>,
{
    let (fri_args, pow) = match args.len() {
        6 => (args, [0, 0]),
        8 => (&args[..6], [args[6], args[7]]),
        _ => panic!("LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW [BATCH_POW OOD_POW]"),
    };
    let [log_blowup, log_final_poly_len, max_log_arity, num_queries, commit_pow, query_pow] =
        fri_args[..]
    else {
        unreachable!()
    };
    let val_mmcs = ValMmcs::<F, P16, P24>::new(Hash::new(p24.clone()), Compress::new(p16), 0);
    let fri = FriParameters {
        log_blowup,
        log_final_poly_len,
        max_log_arity,
        num_queries,
        batch_proof_of_work_bits: pow[0],
        commit_proof_of_work_bits: commit_pow,
        query_proof_of_work_bits: query_pow,
        mmcs: ChallengeMmcs::new(val_mmcs.clone()),
    };
    let pcs = Pcs::new(Radix2DitParallel::default(), val_mmcs, fri);
    Config::new(pcs, Challenger::new(p24)).with_ood_proof_of_work_bits(pow[1])
}

/// Two columns `left, right`: rows `(a, b)` first, `(right, left + right)` next, and `right = x` last.
pub struct FibonacciAir;

impl<T> BaseAir<T> for FibonacciAir {
    fn width(&self) -> usize {
        2
    }

    fn num_public_values(&self) -> usize {
        3
    }
}

impl<AB: AirBuilder> Air<AB> for FibonacciAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let pis = builder.public_values();
        let (a, b, x) = (pis[0], pis[1], pis[2]);
        let local: &[AB::Var] = main.current_slice();
        let next: &[AB::Var] = main.next_slice();
        let mut first = builder.when_first_row();
        first.assert_eq(local[0], a);
        first.assert_eq(local[1], b);
        let mut transition = builder.when_transition();
        transition.assert_eq(local[1], next[0]);
        transition.assert_eq(local[0] + local[1], next[1]);
        builder.when_last_row().assert_eq(local[1], x);
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

    fn num_public_values(&self) -> usize {
        3
    }
}

impl<AB: AirBuilder> Air<AB> for CubeAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let pis = builder.public_values();
        let (a, b, c) = (pis[0], pis[1], pis[2]);
        let local: &[AB::Var] = main.current_slice();
        let next: &[AB::Var] = main.next_slice();
        let mut first = builder.when_first_row();
        first.assert_eq(local[0], a);
        first.assert_eq(local[1], b);
        let x: AB::Expr = local[0].into();
        let mut transition = builder.when_transition();
        transition.assert_eq(x.clone() * x.clone() * x + local[1], next[0]);
        transition.assert_eq(local[1] + AB::Expr::ONE, next[1]);
        builder.when_last_row().assert_eq(local[0], c);
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

/// Two columns `a, b` with `a² = b` on every row, never reading the next row (Plonky3's
/// `SquareAir` of `uni-stark/tests/no_next_row.rs`): the proof does not open the trace at `ζ ω`.
pub struct SquareAir;

impl<T> BaseAir<T> for SquareAir {
    fn width(&self) -> usize {
        2
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![]
    }
}

impl<AB: AirBuilder> Air<AB> for SquareAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let a = main.current(0).unwrap();
        let b = main.current(1).unwrap();
        builder.assert_eq(a * a, b);
    }
}

/// The trace of `n` rows of `SquareAir`: `a = i + 1`, `b = a²` on row `i`.
pub fn square_trace<F: Field>(n: usize) -> RowMajorMatrix<F> {
    let values = (0..n)
        .flat_map(|i| {
            let a = F::from_u32(i as u32 + 1);
            [a, a * a]
        })
        .collect();
    RowMajorMatrix::new(values, 2)
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

impl<AB: AirBuilder> Air<AB> for WideAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local: &[AB::Var] = main.current_slice();
        let next: &[AB::Var] = main.next_slice();
        let mut transition = builder.when_transition();
        for j in 0..WIDE {
            let x: AB::Expr = local[j].into();
            transition.assert_eq(x.clone() * x.clone() * x + local[(j + 1) % WIDE], next[j]);
        }
    }
}

/// The trace of `n` rows of `WideAir` from `xⱼ = j`.
pub fn wide_trace<F: Field>(n: usize) -> RowMajorMatrix<F> {
    let mut values = Vec::with_capacity(WIDE * n);
    let mut row: Vec<F> = (0..WIDE).map(|j| F::from_u32(j as u32)).collect();
    for _ in 0..n {
        values.extend_from_slice(&row);
        row = (0..WIDE).map(|j| row[j] * row[j] * row[j] + row[(j + 1) % WIDE]).collect();
    }
    RowMajorMatrix::new(values, WIDE)
}

/// Two columns `a, b` and two preprocessed columns `p = i mod 2`, `s = (i + 1) mod 6` on row `i`
/// of `n`, with public values `x, y`: rows `(x, y)` first, then `(b, p·a·b + s·(a + b))`
/// (Plonky3's `MulFibPAir` of `uni-stark/tests/mul_fib_pair.rs`, with public values). With
/// `next_row` it also reads the next preprocessed row, `p' + p = 1` on transitions; without, it
/// declares no next preprocessed row and the proof opens the preprocessed trace at `ζ` only.
pub struct PrepAir {
    pub n: usize,
    pub next_row: bool,
}

impl<F: PrimeField64> BaseAir<F> for PrepAir {
    fn width(&self) -> usize {
        2
    }

    fn num_public_values(&self) -> usize {
        2
    }

    fn preprocessed_width(&self) -> usize {
        2
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let values = (0..self.n)
            .flat_map(|i| [F::from_u32((i % 2) as u32), F::from_u32(((i + 1) % 6) as u32)])
            .collect();
        Some(RowMajorMatrix::new(values, 2))
    }

    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        if self.next_row { vec![0, 1] } else { vec![] }
    }
}

impl<AB: AirBuilder> Air<AB> for PrepAir
where
    AB::F: PrimeField64,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let pis = builder.public_values();
        let (x, y) = (pis[0], pis[1]);
        let local: &[AB::Var] = main.current_slice();
        let next: &[AB::Var] = main.next_slice();
        let prep = builder.preprocessed();
        let (p, s) = (prep.current(0).unwrap(), prep.current(1).unwrap());
        let p_next = if self.next_row { prep.next(0) } else { None };
        let mut first = builder.when_first_row();
        first.assert_eq(local[0], x);
        first.assert_eq(local[1], y);
        let mut transition = builder.when_transition();
        transition.assert_eq(local[1], next[0]);
        transition.assert_eq(p * local[0] * local[1] + s * (local[0] + local[1]), next[1]);
        if let Some(p_next) = p_next {
            transition.assert_eq(p_next + p, AB::Expr::ONE);
        }
    }
}

/// The trace of `n` rows of `PrepAir` from `(1, 2)`, and its public values.
pub fn prep_trace<F: Field>(n: usize) -> (RowMajorMatrix<F>, Vec<F>) {
    let mut values = Vec::with_capacity(2 * n);
    let (mut a, mut b) = (F::ONE, F::TWO);
    for i in 0..n {
        values.push(a);
        values.push(b);
        let (p, s) = (F::from_u32((i % 2) as u32), F::from_u32(((i + 1) % 6) as u32));
        (a, b) = (b, p * a * b + s * (a + b));
    }
    (RowMajorMatrix::new(values, 2), vec![F::ONE, F::TWO])
}

/// Two columns, each the periodic column of the same index (Plonky3's `PeriodicAir` of
/// `uni-stark/tests/periodic_air.rs`).
#[derive(Clone)]
pub struct PeriodicAir<F> {
    pub periodic: Vec<Vec<F>>,
}

impl<F: PrimeField64> PeriodicAir<F> {
    /// Plonky3's periods: `1, 2, 3, 4` and `10, 20`.
    pub fn new() -> Self {
        let tens = vec![F::from_u32(10), F::from_u32(20)];
        Self { periodic: vec![(1..=4).map(F::from_u32).collect(), tens] }
    }

    /// A constant column and one of period 32 (Plonky3's `wide_period_range` test).
    pub fn wide() -> Self {
        Self { periodic: vec![vec![F::from_u32(7)], (0..32).map(F::from_u32).collect()] }
    }

    /// A constant column and one of period 2 (Plonky3's `tiny_quotient` test, on two rows).
    pub fn tiny() -> Self {
        Self { periodic: vec![vec![F::from_u32(9)], vec![F::ONE, F::TWO]] }
    }

    /// The trace of `n` rows: each column its periodic column.
    pub fn trace(&self, n: usize) -> RowMajorMatrix<F> {
        let values = (0..n)
            .flat_map(|i| self.periodic.iter().map(move |c| c[i % c.len()]))
            .collect();
        RowMajorMatrix::new(values, 2)
    }
}

impl<F: Field> BaseAir<F> for PeriodicAir<F> {
    fn width(&self) -> usize {
        2
    }

    fn num_periodic_columns(&self) -> usize {
        self.periodic.len()
    }

    fn periodic_columns(&self) -> std::borrow::Cow<'_, [Vec<F>]> {
        std::borrow::Cow::Borrowed(&self.periodic)
    }
}

impl<AB: AirBuilder> Air<AB> for PeriodicAir<AB::F>
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let p0: AB::Expr = builder.periodic_values()[0].into();
        let p1: AB::Expr = builder.periodic_values()[1].into();
        builder.assert_eq(local[0], p0);
        builder.assert_eq(local[1], p1);
    }
}

/// Columns `x, y`, a constant periodic column `k = 3` and one `s` of period `1, 2, 3, 4`, with
/// public values `a, c`: `x = a` first, `(k x³ + s y, y + s)` next, `x = c` last. With periodic
/// columns Plonky3 sizes the quotient by polynomial degrees: two chunks, where the degree
/// multiple would give four.
pub struct PeriodicCubeAir<F> {
    pub periodic: Vec<Vec<F>>,
}

impl<F: PrimeField64> PeriodicCubeAir<F> {
    pub fn new() -> Self {
        Self { periodic: vec![vec![F::from_u32(3)], (1..=4).map(F::from_u32).collect()] }
    }

    /// The trace of `n` rows from `(2, 0)`, and its public values.
    pub fn trace(&self, n: usize) -> (RowMajorMatrix<F>, Vec<F>) {
        let mut values = Vec::with_capacity(2 * n);
        let (mut x, mut y) = (F::TWO, F::ZERO);
        for i in 0..n {
            values.push(x);
            values.push(y);
            let s = self.periodic[1][i % 4];
            (x, y) = (F::from_u32(3) * x * x * x + s * y, y + s);
        }
        let last = values[2 * n - 2];
        (RowMajorMatrix::new(values, 2), vec![F::TWO, last])
    }
}

impl<F: Field> BaseAir<F> for PeriodicCubeAir<F> {
    fn width(&self) -> usize {
        2
    }

    fn num_public_values(&self) -> usize {
        2
    }

    fn num_periodic_columns(&self) -> usize {
        self.periodic.len()
    }

    fn periodic_columns(&self) -> std::borrow::Cow<'_, [Vec<F>]> {
        std::borrow::Cow::Borrowed(&self.periodic)
    }
}

impl<AB: AirBuilder> Air<AB> for PeriodicCubeAir<AB::F>
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let pis = builder.public_values();
        let (a, c) = (pis[0], pis[1]);
        let local: &[AB::Var] = main.current_slice();
        let next: &[AB::Var] = main.next_slice();
        let k: AB::Expr = builder.periodic_values()[0].into();
        let s: AB::Expr = builder.periodic_values()[1].into();
        builder.when_first_row().assert_eq(local[0], a);
        let x: AB::Expr = local[0].into();
        let mut transition = builder.when_transition();
        transition.assert_eq(k * x.clone() * x.clone() * x + s.clone() * local[1], next[0]);
        transition.assert_eq(local[1] + s, next[1]);
        builder.when_last_row().assert_eq(local[0], c);
    }
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

/// A proof of `air` (`fib`, `cube`, `square`, `wide`, `prep` and `prep0`, `PrepAir` with and without its
/// next preprocessed row, `periodic`, `periodic-wide` and `periodic-tiny`, `PeriodicAir` with
/// Plonky3's periods, or `pcube`, `PeriodicCubeAir`) on `2^log_n` rows, checked by Plonky3's
/// verifier.
pub fn prove_air<F, P16, P24>(config: &Config<F, P16, P24>, air: &str, log_n: usize)
    -> Proof<Config<F, P16, P24>>
where
    F: TwoAdicField + PrimeField64 + BinomiallyExtendable<4>,
    P16: CryptographicPermutation<[F; 16]> + CryptographicPermutation<[F::Packing; 16]>,
    P24: CryptographicPermutation<[F; 24]> + CryptographicPermutation<[F::Packing; 24]>,
{
    let n = 1 << log_n;
    match air {
        "fib" => {
            let (trace, x) = trace::<F>(n);
            let pis = vec![F::ZERO, F::ONE, x];
            let proof = prove(config, &FibonacciAir, trace, &pis).expect("Plonky3 cannot prove");
            verify(config, &FibonacciAir, &proof, &pis).expect("Plonky3 rejects its own proof");
            proof
        }
        "cube" => {
            let (trace, x) = cube_trace::<F>(n);
            let pis = vec![F::TWO, F::ZERO, x];
            let proof = prove(config, &CubeAir, trace, &pis).expect("Plonky3 cannot prove");
            verify(config, &CubeAir, &proof, &pis).expect("Plonky3 rejects its own proof");
            proof
        }
        "square" => {
            let proof =
                prove(config, &SquareAir, square_trace::<F>(n), &[]).expect("Plonky3 cannot prove");
            verify(config, &SquareAir, &proof, &[]).expect("Plonky3 rejects its own proof");
            proof
        }
        "wide" => {
            let proof = prove(config, &WideAir, wide_trace::<F>(n), &[]).expect("Plonky3 cannot prove");
            verify(config, &WideAir, &proof, &[]).expect("Plonky3 rejects its own proof");
            proof
        }
        "prep" | "prep0" => {
            let air = PrepAir { n, next_row: air == "prep" };
            let (data, vk) = setup_preprocessed(config, &air, log_n)
                .expect("Plonky3 cannot commit")
                .expect("no preprocessed columns");
            let (trace, pis) = prep_trace::<F>(n);
            let proof = prove_with_preprocessed(config, &air, trace, &pis, Some(&data))
                .expect("Plonky3 cannot prove");
            verify_with_preprocessed(config, &air, &proof, &pis, Some(&vk))
                .expect("Plonky3 rejects its own proof");
            proof
        }
        "periodic" | "periodic-wide" | "periodic-tiny" => {
            let air = match air {
                "periodic" => PeriodicAir::new(),
                "periodic-wide" => PeriodicAir::wide(),
                _ => PeriodicAir::tiny(),
            };
            let proof = prove(config, &air, air.trace(n), &[]).expect("Plonky3 cannot prove");
            verify(config, &air, &proof, &[]).expect("Plonky3 rejects its own proof");
            proof
        }
        "pcube" => {
            let air = PeriodicCubeAir::new();
            let (trace, pis) = air.trace(n);
            let proof = prove(config, &air, trace, &pis).expect("Plonky3 cannot prove");
            verify(config, &air, &proof, &pis).expect("Plonky3 rejects its own proof");
            proof
        }
        _ => panic!("unknown AIR {air}"),
    }
}

fn koalabear_config(args: &[usize]) -> Config<F, p3_koala_bear::Poseidon2KoalaBear<16>,
    p3_koala_bear::Poseidon2KoalaBear<24>> {
    config(default_koalabear_poseidon2_16(), default_koalabear_poseidon2_24(), args)
}

/// `stark AIR LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW [BATCH_POW
/// OOD_POW]`, `AIR` one of `fib`, `cube`, `square`, `wide`, `prep`, `prep0`, `periodic`, `periodic-wide`,
/// `periodic-tiny`, `pcube`: the proof as JSON, after Plonky3 verified it. Run with
/// `RAYON_NUM_THREADS=1` for the smallest grinding witnesses.
pub fn stark(air: &str, args: &[usize]) {
    let config = koalabear_config(&args[1..]);
    let proof = prove_air(&config, air, args[0]);
    println!("{}", serde_json::to_string(&proof).unwrap());
}

/// A fixed sequence on the STARK challenger: observe `0, …, 19`, sample two base elements and an
/// extension element, observe `7` and an extension element, sample 10 bits, grind 6 bits, and
/// sample once more. Canonical values. Run with `RAYON_NUM_THREADS=1`.
pub fn challenger() {
    use p3_challenger::{CanObserve, CanSample, CanSampleBits, FieldChallenger, GrindingChallenger};
    use p3_field::{BasedVectorSpace, PrimeField32};
    let mut c = Challenger::<F, _>::new(default_koalabear_poseidon2_24());
    for i in 0..20u32 {
        c.observe(F::from_u32(i));
    }
    let a: F = c.sample();
    let b: F = c.sample();
    let e: Challenge<F> = c.sample_algebra_element();
    c.observe(F::from_u32(7));
    c.observe_algebra_element(Challenge::<F>::from_basis_coefficients_fn(|i| F::from_u32(100 + i as u32)));
    let bits = c.sample_bits(10);
    let w = c.grind(6);
    let z: F = c.sample();
    let ext: Vec<u32> = BasedVectorSpace::<F>::as_basis_coefficients_slice(&e).iter().map(|x| x.as_canonical_u32()).collect();
    println!("challenger {} {} {:?} {} {} {}", a.as_canonical_u32(), b.as_canonical_u32(), ext, bits,
        w.as_canonical_u32(), z.as_canonical_u32());
}

/// `prove-bench AIR LOG_N LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW
/// [BATCH_POW OOD_POW]`: the median milliseconds of seven proofs.
pub fn prove_bench(air: &str, args: &[usize]) {
    use std::time::Instant;
    let log_n = args[0];
    let config = koalabear_config(&args[1..]);
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
        std::hint::black_box(proof.expect("Plonky3 cannot prove"));
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
