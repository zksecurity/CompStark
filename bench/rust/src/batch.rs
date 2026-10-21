//! Plonky3 `batch-stark` proofs for known-answer tests, on the configuration of `stark.rs`: the
//! test AIRs of `batch-stark/tests/simple.rs` (a Fibonacci AIR with a preprocessed index column,
//! `MulAir`, `PeriodicAir`, `PreprocessedMulAir`, and the lookup AIRs `MulAirLookups`,
//! `FibAirLookups` and `SingleTableLocalLookupAir`), batched at mixed heights.
use p3_air::{Air, AirBuilder, BaseAir, PermutationAirBuilder, WindowAccess};
use p3_lookup::{Count, InteractionBuilder};
use p3_batch_stark::{prove_batch, verify_batch, ProverData, StarkInstance};
use p3_baby_bear::{default_babybear_poseidon2_16, default_babybear_poseidon2_24};
use p3_field::extension::BinomiallyExtendable;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_koala_bear::{default_koalabear_poseidon2_16, default_koalabear_poseidon2_24};
use p3_matrix::dense::RowMajorMatrix;
use p3_symmetric::CryptographicPermutation;

use crate::stark::{
    config, square_trace, trace, wide_trace, Config, FibonacciAir, PeriodicAir, SquareAir, WideAir,
    WIDE,
};

/// The AIRs of a batch, as Plonky3's `DemoAir`.
#[derive(Clone)]
pub enum BatchAir<F> {
    /// `FibonacciAir` of `simple.rs`: the Fibonacci AIR with an unread preprocessed column holding
    /// the row index, on `2^log_height` rows.
    Fib { log_height: usize },
    /// `MulAir` with `reps` repetitions: columns `a, b, c` per repetition with `a b = c`, and
    /// `(b, a + b)` next; one more unconstrained column.
    Mul { reps: usize },
    /// `PeriodicAir`.
    Periodic(PeriodicAir<F>),
    /// `PreprocessedMulAir`: `main = multiplier · prep`, the preprocessed column the row index,
    /// not read at the next row.
    PrepMul { log_height: usize, multiplier: u64 },
    /// `SquareAir`, which never reads the next row.
    Square,
    /// `WideAir`, the benchmarks' wide table.
    Wide,
    /// `MulAirLookups`: `MulAir` with `reps` repetitions, with a local lookup of each `a` against
    /// the last column if `local`, and sending `(a, b)` of repetition `i` on bus `global[i]` with
    /// multiplicity `-1` if `global` is not empty.
    MulL { reps: usize, local: bool, global: Vec<String> },
    /// `FibAirLookups`: `Fib`, receiving `(left, right)` on `bus` with the multiplicity `count`
    /// (`FibAirLookups` with `name_and_mult`, here signed) if any.
    FibL { log_height: usize, bus: Option<(String, i64)> },
    /// `SingleTableLocalLookupAir`: three local lookups with selector multiplicities.
    SingleLocal,
}

impl<F: PrimeField64> BaseAir<F> for BatchAir<F> {
    fn width(&self) -> usize {
        match self {
            Self::Fib { .. } | Self::FibL { .. } | Self::Periodic(_) | Self::Square => 2,
            Self::Mul { reps } | Self::MulL { reps, .. } => 3 * reps + 1,
            Self::SingleLocal => 7,
            Self::PrepMul { .. } => 1,
            Self::Wide => WIDE,
        }
    }

    fn num_public_values(&self) -> usize {
        if let Self::Fib { .. } | Self::FibL { .. } = self { 3 } else { 0 }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            Self::Fib { log_height }
            | Self::FibL { log_height, .. }
            | Self::PrepMul { log_height, .. } => {
                Some(RowMajorMatrix::new((0..1u64 << log_height).map(F::from_u64).collect(), 1))
            }
            _ => None,
        }
    }

    fn preprocessed_width(&self) -> usize {
        match self {
            Self::Fib { .. } | Self::FibL { .. } | Self::PrepMul { .. } => 1,
            _ => 0,
        }
    }

    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        match self {
            Self::Fib { .. } | Self::FibL { .. } => vec![0],
            _ => vec![],
        }
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        if let Self::Square = self { vec![] } else { (0..BaseAir::<F>::width(self)).collect() }
    }

    fn num_periodic_columns(&self) -> usize {
        if let Self::Periodic(a) = self { a.periodic.len() } else { 0 }
    }

    fn periodic_columns(&self) -> std::borrow::Cow<'_, [Vec<F>]> {
        match self {
            Self::Periodic(a) => std::borrow::Cow::Borrowed(&a.periodic),
            _ => std::borrow::Cow::Owned(vec![]),
        }
    }
}

impl<AB: PermutationAirBuilder + InteractionBuilder> Air<AB> for BatchAir<AB::F>
where
    AB::F: PrimeField64,
{
    fn eval(&self, builder: &mut AB) {
        match self {
            Self::Fib { .. } => FibonacciAir.eval(builder),
            Self::FibL { bus, .. } => {
                FibonacciAir.eval(builder);
                if let Some((name, count)) = bus {
                    let main = builder.main();
                    let (left, right) = (main.current(0).unwrap(), main.current(1).unwrap());
                    let c = if *count < 0 {
                        -AB::Expr::from_u64(count.unsigned_abs())
                    } else {
                        AB::Expr::from_u64(*count as u64)
                    };
                    builder.push_interaction(name, [left.into(), right.into()],
                        Count::bounded(c, count.unsigned_abs() as u32));
                }
            }
            Self::MulL { reps, local, global } => {
                Self::Mul { reps: *reps }.eval(builder);
                let main = builder.main();
                let row = main.current_slice();
                let lut = row[3 * reps];
                for rep in 0..*reps {
                    let (a, b) = (row[3 * rep], row[3 * rep + 1]);
                    if *local {
                        builder.push_local_interaction(vec![
                            (vec![a.into()], Count::bounded(AB::Expr::ONE, 1)),
                            (vec![lut.into()], Count::provided(-AB::Expr::ONE)),
                        ]);
                    }
                    if !global.is_empty() {
                        builder.push_interaction(&global[rep], [a.into(), b.into()], -1);
                    }
                }
            }
            Self::SingleLocal => {
                let main = builder.main();
                let local = main.current_slice();
                let (s1, s2, s3, table) = (local[0], local[1], local[2], local[3]);
                let (m1, m2, m3) = (local[4], local[5], local[6]);
                let is_first = builder.is_first_row();
                let is_trans = builder.is_transition();
                let is_last = builder.is_last_row();
                builder.push_local_interaction(vec![
                    (vec![s1.into()], Count::bounded(is_first.clone(), 1)),
                    (vec![table.into()], Count::provided(-(is_first * m1.into()))),
                ]);
                builder.push_local_interaction(vec![
                    (vec![s2.into()], Count::bounded(is_trans.clone(), 1)),
                    (vec![table.into()], Count::provided(-(is_trans * m2.into()))),
                ]);
                builder.push_local_interaction(vec![
                    (vec![s3.into()], Count::bounded(is_last.clone(), 1)),
                    (vec![table.into()], Count::provided(-(is_last * m3.into()))),
                ]);
            }
            Self::Square => SquareAir.eval(builder),
            Self::Wide => WideAir.eval(builder),
            Self::Periodic(a) => a.eval(builder),
            Self::Mul { reps } => {
                let main = builder.main();
                let local = main.current_slice();
                let next = main.next_slice();
                for i in 0..*reps {
                    let s = 3 * i;
                    let (a, b, c) = (local[s], local[s + 1], local[s + 2]);
                    builder.assert_eq(a * b, c);
                    builder.when_transition().assert_eq(b, next[s]);
                    builder.when_transition().assert_eq(a + b, next[s + 1]);
                }
            }
            Self::PrepMul { multiplier, .. } => {
                let main = builder.main();
                let local = main.current_slice();
                let prep = builder.preprocessed().current(0).unwrap();
                builder.assert_eq(local[0], prep * AB::Expr::from_u64(*multiplier));
            }
        }
    }
}

/// `mul_trace` of `simple.rs`: `rows` rows of `MulAir` with `reps` repetitions.
fn mul_trace<F: Field>(rows: usize, reps: usize) -> RowMajorMatrix<F> {
    let w = 3 * reps + 1;
    let mut v = F::zero_vec(rows * w);
    for rep in 0..reps {
        let (mut a, mut b) = (F::ZERO, F::ONE);
        for i in 0..rows {
            let idx = i * w + 3 * rep;
            v[idx] = a;
            v[idx + 1] = b;
            v[idx + 2] = a * b;
            if i != rows - 1 {
                v[i * w + w - 1] = b;
            }
            (a, b) = (b, a + b);
        }
    }
    RowMajorMatrix::new(v, w)
}

/// `single_table_local_lookup_trace` of `simple.rs`.
fn single_local_trace<F: Field>(n: usize) -> RowMajorMatrix<F> {
    let w = 7;
    let mut v = F::zero_vec(n * w);
    for i in 0..n {
        v[i * w] = F::from_u64((n - 1) as u64);
        v[i * w + 1] = F::from_u64(if i < n - 1 { (n - i - 1) as u64 } else { 11 });
        if i != n - 1 {
            v[i * w + 2] = F::from_u64(11);
        }
        v[i * w + 3] = F::from_u64((n - i - 1) as u64);
        v[i * w + 4] = F::from_bool(i == 0);
        v[i * w + 5] = F::from_bool(i < n - 1);
        v[i * w + 6] = F::from_bool(i == n - 1);
    }
    RowMajorMatrix::new(v, w)
}

/// An instance of `FibL` on `2^log_n` rows starting at the Fibonacci pair `(F_k, F_{k+1})`.
fn fib_from<F: PrimeField64>(log_n: usize, k: usize, bus: &str, count: i64)
    -> (BatchAir<F>, RowMajorMatrix<F>, Vec<F>) {
    let n = 1 << log_n;
    let (mut a, mut b) = (F::ZERO, F::ONE);
    for _ in 0..k {
        (a, b) = (b, a + b);
    }
    let (a0, b0) = (a, b);
    let mut v = Vec::with_capacity(2 * n);
    for _ in 0..n {
        v.extend([a, b]);
        (a, b) = (b, a + b);
    }
    let air = BatchAir::FibL { log_height: log_n, bus: Some((bus.to_string(), count)) };
    let x = v[2 * n - 1];
    (air, RowMajorMatrix::new(v, 2), vec![a0, b0, x])
}

/// An instance of `air` on `2^log_n` rows: the AIR, its trace and its public values.
fn instance<F: PrimeField64>(air: BatchAir<F>, log_n: usize)
    -> (BatchAir<F>, RowMajorMatrix<F>, Vec<F>) {
    let n = 1 << log_n;
    match &air {
        BatchAir::Fib { .. } => {
            let (t, x) = trace::<F>(n);
            (air, t, vec![F::ZERO, F::ONE, x])
        }
        BatchAir::Mul { reps } | BatchAir::MulL { reps, .. } => {
            let t = mul_trace(n, *reps);
            (air, t, vec![])
        }
        BatchAir::FibL { .. } => {
            let (t, x) = trace::<F>(n);
            (air, t, vec![F::ZERO, F::ONE, x])
        }
        BatchAir::SingleLocal => (air, single_local_trace(n), vec![]),
        BatchAir::Periodic(a) => {
            let t = a.trace(n);
            (air, t, vec![])
        }
        BatchAir::Square => {
            let t = square_trace(n);
            (air, t, vec![])
        }
        BatchAir::Wide => {
            let t = wide_trace(n);
            (air, t, vec![])
        }
        BatchAir::PrepMul { multiplier, .. } => {
            let m = *multiplier;
            let t = RowMajorMatrix::new((0..n as u64).map(|i| F::from_u64(i * m)).collect(), 1);
            (air, t, vec![])
        }
    }
}

/// The instances of a batch: `three` (`test_three_instances_mixed_sizes`), `mixed`
/// (`test_mixed_preprocessed`), `periodic` (`test_periodic_air`), `single` (`test_single_instance`)
/// `prepmul`, preprocessed traces at mixed heights with and without next-row reads, and `square`,
/// an AIR that does not read the next row beside one that does; and the benchmark `wide`, three
/// `WideAir` tables of `2^20`, `2^19` and `2^16` rows.
pub fn case<F: PrimeField64>(name: &str) -> Vec<(BatchAir<F>, RowMajorMatrix<F>, Vec<F>)> {
    match name {
        "three" => vec![instance(BatchAir::Fib { log_height: 4 }, 4),
            instance(BatchAir::Mul { reps: 2 }, 3), instance(BatchAir::Fib { log_height: 3 }, 3)],
        "mixed" => vec![instance(BatchAir::Fib { log_height: 4 }, 4),
            instance(BatchAir::Mul { reps: 2 }, 4)],
        "periodic" => vec![instance(BatchAir::Periodic(PeriodicAir::new()), 6)],
        "single" => vec![instance(BatchAir::Fib { log_height: 5 }, 5)],
        "prepmul" => vec![instance(BatchAir::PrepMul { log_height: 4, multiplier: 2 }, 4),
            instance(BatchAir::Fib { log_height: 5 }, 5), instance(BatchAir::Mul { reps: 1 }, 3)],
        "square" => vec![instance(BatchAir::Square, 4), instance(BatchAir::Fib { log_height: 3 }, 3)],
        "wide" => vec![instance(BatchAir::Wide, 20), instance(BatchAir::Wide, 19),
            instance(BatchAir::Wide, 16)],
        "local1" => vec![instance(mul_l(1, true, &[]), 3)],
        "local" => vec![instance(mul_l(2, true, &[]), 4),
            instance(BatchAir::FibL { log_height: 4, bus: None }, 4)],
        "global" => vec![instance(mul_l(2, false, &["MulFib", "MulFib"]), 3), fib_l(3, "MulFib", 2)],
        "both" => vec![instance(mul_l(2, true, &["MulFib", "MulFib"]), 4), fib_l(4, "MulFib", 2)],
        "lookups" => vec![instance(mul_l(2, true, &["MulFib1", "MulFib2"]), 4),
            instance(BatchAir::FibL { log_height: 3, bus: None }, 3), fib_l(4, "MulFib1", 1),
            instance(mul_l(2, false, &[]), 3), fib_l(4, "MulFib2", 1),
            instance(mul_l(2, true, &[]), 4)],
        "single-local" => vec![instance(BatchAir::SingleLocal, 3)],
        "heights" => vec![fib_from(3, 0, "Fib", -1), instance(mul_l(1, true, &[]), 2),
            fib_from(4, 0, "Fib", 1), fib_from(3, 8, "Fib", -1)],
        "failed-global" => vec![instance(mul_l(2, false, &["MulFib1", "MulFib2"]), 3),
            fib_l(3, "MulFib1", 1)],
        "failed-local" => {
            let (air, mut t, pis) = instance(mul_l(2, true, &[]), 3);
            t.values[6] = F::from_u64(9999);
            vec![(air, t, pis)]
        }
        _ => panic!("unknown batch {name}"),
    }
}

/// `MulAirLookups` with `reps` repetitions, local lookups if `local`, and the global buses
/// `global`.
fn mul_l<F>(reps: usize, local: bool, global: &[&str]) -> BatchAir<F> {
    BatchAir::MulL { reps, local, global: global.iter().map(|s| s.to_string()).collect() }
}

/// `FibAirLookups` on `2^log_n` rows receiving on `bus` with multiplicity `count`.
fn fib_l<F: PrimeField64>(log_n: usize, bus: &str, count: i64)
    -> (BatchAir<F>, RowMajorMatrix<F>, Vec<F>) {
    instance(BatchAir::FibL { log_height: log_n, bus: Some((bus.to_string(), count)) }, log_n)
}

/// The batch proof of `name` on `config`, after Plonky3 verified it.
fn prove_case<F, P16, P24>(config: &Config<F, P16, P24>, name: &str) -> String
where
    F: TwoAdicField + PrimeField64 + BinomiallyExtendable<4>,
    P16: CryptographicPermutation<[F; 16]> + CryptographicPermutation<[F::Packing; 16]>,
    P24: CryptographicPermutation<[F; 24]> + CryptographicPermutation<[F::Packing; 24]>,
{
    let insts = case::<F>(name);
    let instances: Vec<StarkInstance<'_, _, BatchAir<F>>> = insts.iter()
        .map(|(air, trace, pis)| StarkInstance { air, trace, public_values: pis.clone() })
        .collect();
    let prover_data =
        ProverData::from_instances(config, &instances).expect("Plonky3 cannot commit");
    let proof = prove_batch(config, &instances, &prover_data).expect("Plonky3 cannot prove");
    let airs: Vec<BatchAir<F>> = insts.iter().map(|(a, _, _)| a.clone()).collect();
    let pvs: Vec<Vec<F>> = insts.iter().map(|(_, _, p)| p.clone()).collect();
    let verdict = verify_batch(config, &airs, &proof, &pvs, &prover_data.common);
    if name.starts_with("failed") {
        verdict.expect_err("Plonky3 accepts an unbalanced batch");
    } else {
        verdict.expect("Plonky3 rejects its own proof");
    }
    serde_json::to_string(&proof).unwrap()
}

/// `batch CASE LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW [BATCH_POW
/// OOD_POW]`: the batch proof of `case` over KoalaBear as JSON, after Plonky3 verified it. Run
/// with `RAYON_NUM_THREADS=1` for the smallest grinding witnesses.
pub fn batch(name: &str, args: &[usize]) {
    let config = config(default_koalabear_poseidon2_16(), default_koalabear_poseidon2_24(), args);
    println!("{}", prove_case(&config, name));
}

/// `batch-babybear CASE …`: the same over BabyBear.
pub fn batch_babybear(name: &str, args: &[usize]) {
    let config = config(default_babybear_poseidon2_16(), default_babybear_poseidon2_24(), args);
    println!("{}", prove_case(&config, name));
}

/// `batch-bench CASE …`: the median milliseconds of seven `prove_batch` calls over KoalaBear,
/// without the common data's setup.
pub fn batch_bench(name: &str, args: &[usize]) {
    use std::time::Instant;
    let config = config(default_koalabear_poseidon2_16(), default_koalabear_poseidon2_24(), args);
    let insts = case::<p3_koala_bear::KoalaBear>(name);
    let instances: Vec<StarkInstance<'_, _, _>> = insts.iter()
        .map(|(air, trace, pis)| StarkInstance { air, trace, public_values: pis.clone() })
        .collect();
    let prover_data =
        ProverData::from_instances(&config, &instances).expect("Plonky3 cannot commit");
    let mut samples = vec![];
    for _ in 0..7 {
        let t = Instant::now();
        let proof = prove_batch(&config, &instances, &prover_data).expect("Plonky3 cannot prove");
        samples.push(t.elapsed().as_secs_f64() * 1000.0);
        std::hint::black_box(proof);
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("plonky3 prove_batch {name} ms median {:.2}", samples[3]);
}
