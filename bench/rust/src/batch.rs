//! Plonky3 `batch-stark` proofs for known-answer tests, on the configuration of `stark.rs`: the
//! test AIRs of `batch-stark/tests/simple.rs` (a Fibonacci AIR with a preprocessed index column,
//! `MulAir`, `PeriodicAir` and `PreprocessedMulAir`), batched at mixed heights.
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_batch_stark::{prove_batch, verify_batch, ProverData, StarkInstance};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::{default_koalabear_poseidon2_16, default_koalabear_poseidon2_24, KoalaBear};
use p3_matrix::dense::RowMajorMatrix;

use crate::stark::{config, trace, FibonacciAir, PeriodicAir};

type F = KoalaBear;

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
}

impl<F: PrimeField64> BaseAir<F> for BatchAir<F> {
    fn width(&self) -> usize {
        match self {
            Self::Fib { .. } | Self::Periodic(_) => 2,
            Self::Mul { reps } => 3 * reps + 1,
            Self::PrepMul { .. } => 1,
        }
    }

    fn num_public_values(&self) -> usize {
        if let Self::Fib { .. } = self { 3 } else { 0 }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            Self::Fib { log_height } | Self::PrepMul { log_height, .. } => {
                Some(RowMajorMatrix::new((0..1u64 << log_height).map(F::from_u64).collect(), 1))
            }
            _ => None,
        }
    }

    fn preprocessed_width(&self) -> usize {
        match self {
            Self::Fib { .. } | Self::PrepMul { .. } => 1,
            _ => 0,
        }
    }

    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        match self {
            Self::Fib { .. } => vec![0],
            _ => vec![],
        }
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

impl<AB: AirBuilder> Air<AB> for BatchAir<AB::F>
where
    AB::F: PrimeField64,
{
    fn eval(&self, builder: &mut AB) {
        match self {
            Self::Fib { .. } => FibonacciAir.eval(builder),
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
fn mul_trace(rows: usize, reps: usize) -> RowMajorMatrix<F> {
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

/// An instance of `air` on `2^log_n` rows: the AIR, its trace and its public values.
fn instance(air: BatchAir<F>, log_n: usize) -> (BatchAir<F>, RowMajorMatrix<F>, Vec<F>) {
    let n = 1 << log_n;
    match &air {
        BatchAir::Fib { .. } => {
            let (t, x) = trace::<F>(n);
            (air, t, vec![F::ZERO, F::ONE, x])
        }
        BatchAir::Mul { reps } => {
            let t = mul_trace(n, *reps);
            (air, t, vec![])
        }
        BatchAir::Periodic(a) => {
            let t = a.trace(n);
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
/// and `prepmul`, preprocessed traces at mixed heights with and without next-row reads.
pub fn case(name: &str) -> Vec<(BatchAir<F>, RowMajorMatrix<F>, Vec<F>)> {
    match name {
        "three" => vec![instance(BatchAir::Fib { log_height: 4 }, 4),
            instance(BatchAir::Mul { reps: 2 }, 3), instance(BatchAir::Fib { log_height: 3 }, 3)],
        "mixed" => vec![instance(BatchAir::Fib { log_height: 4 }, 4),
            instance(BatchAir::Mul { reps: 2 }, 4)],
        "periodic" => vec![instance(BatchAir::Periodic(PeriodicAir::new()), 6)],
        "single" => vec![instance(BatchAir::Fib { log_height: 5 }, 5)],
        "prepmul" => vec![instance(BatchAir::PrepMul { log_height: 4, multiplier: 2 }, 4),
            instance(BatchAir::Fib { log_height: 5 }, 5), instance(BatchAir::Mul { reps: 1 }, 3)],
        _ => panic!("unknown batch {name}"),
    }
}

/// `batch CASE LOG_BLOWUP LOG_FINAL MAX_LOG_ARITY QUERIES COMMIT_POW QUERY_POW [BATCH_POW
/// OOD_POW]`: the batch proof of `case` as JSON, after Plonky3 verified it. Run with
/// `RAYON_NUM_THREADS=1` for the smallest grinding witnesses.
pub fn batch(name: &str, args: &[usize]) {
    let config = config(default_koalabear_poseidon2_16(), default_koalabear_poseidon2_24(), args);
    let insts = case(name);
    let instances: Vec<StarkInstance<'_, _, BatchAir<F>>> = insts.iter()
        .map(|(air, trace, pis)| StarkInstance { air, trace, public_values: pis.clone() })
        .collect();
    let prover_data =
        ProverData::from_instances(&config, &instances).expect("Plonky3 cannot commit");
    let proof = prove_batch(&config, &instances, &prover_data).expect("Plonky3 cannot prove");
    let airs: Vec<BatchAir<F>> = insts.iter().map(|(a, _, _)| a.clone()).collect();
    let pvs: Vec<Vec<F>> = insts.iter().map(|(_, _, p)| p.clone()).collect();
    verify_batch(&config, &airs, &proof, &pvs, &prover_data.common)
        .expect("Plonky3 rejects its own proof");
    println!("{}", serde_json::to_string(&proof).unwrap());
}
