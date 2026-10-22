//! Plonky3's example `examples/examples/prove_prime_field_31.rs --field koala-bear --objective
//! keccak-f-permutations --merkle-hash poseidon2` at revision `a4982ec`, reproduced from the same
//! upstream functions, since the example binary does not write its proof: `SmallRng` seeded with
//! `1` draws the width-16 and then the width-24 Poseidon2 constants (`new_from_rng_128`), the
//! Merkle commitment is `MerkleTreeMmcs` with cap height 3, FRI is `new_benchmark_high_arity`
//! with the example's query count for 100 conjectured bits, and the trace is
//! `KeccakAir::generate_random_trace_rows` of `2^L / 24` permutations. The proof's postcard size
//! is the example's `Proof size` line, so a run of both shows that the configurations agree.
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeField32};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_keccak_air::KeccakAir;
use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_poseidon2::ExternalLayerConstants;
use p3_symmetric::{PaddingFreeSponge, Permutation, TruncatedPermutation};
use p3_uni_stark::{prove, verify, ConjecturedSecurity, StarkConfig};
use rand::distr::StandardUniform;
use rand::rngs::SmallRng;
use rand::{RngExt, SeedableRng};

type F = KoalaBear;
type EF = BinomialExtensionField<F, 4>;
type P16 = Poseidon2KoalaBear<16>;
type P24 = Poseidon2KoalaBear<24>;
type ValMmcs = MerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing,
    PaddingFreeSponge<P24, 24, 16, 8>, TruncatedPermutation<P16, 2, 8, 16>, 2, 8>;
type ChallengeMmcs = ExtensionMmcs<F, EF, ValMmcs>;
pub type ExampleConfig = StarkConfig<TwoAdicFriPcs<F, Radix2DitParallel<F>, ValMmcs, ChallengeMmcs>,
    EF, DuplexChallenger<F, P24, 24, 16>>;

/// The round constants of one Poseidon2 instance as `new_from_rng` draws them: the initial and
/// terminal full rounds' and the partial rounds'.
pub struct Constants<const W: usize> {
    pub initial: Vec<[F; W]>,
    pub terminal: Vec<[F; W]>,
    pub internal: Vec<F>,
}

/// The constants `new_from_rng` draws from `rng` with four initial and four terminal full rounds
/// and `partial` partial rounds.
fn draw<const W: usize>(rng: &mut SmallRng, partial: usize) -> Constants<W>
where
    StandardUniform: rand::distr::Distribution<[F; W]>,
{
    let initial = rng.sample_iter::<[F; W], _>(StandardUniform).take(4).collect();
    let terminal = rng.sample_iter::<[F; W], _>(StandardUniform).take(4).collect();
    let internal = rng.sample_iter::<F, _>(StandardUniform).take(partial).collect();
    Constants { initial, terminal, internal }
}

/// The example's Poseidon2 instances and their constants, which are checked to give the same
/// permutations as `new_from_rng_128`.
pub fn poseidon2() -> (P16, P24, Constants<16>, Constants<24>) {
    let mut rng = SmallRng::seed_from_u64(1);
    let p16 = P16::new_from_rng_128(&mut rng);
    let p24 = P24::new_from_rng_128(&mut rng);
    let mut rng = SmallRng::seed_from_u64(1);
    let c16 = draw::<16>(&mut rng, 20);
    let c24 = draw::<24>(&mut rng, 23);
    let q16 = P16::new(ExternalLayerConstants::new(c16.initial.clone(), c16.terminal.clone()),
        c16.internal.clone());
    let q24 = P24::new(ExternalLayerConstants::new(c24.initial.clone(), c24.terminal.clone()),
        c24.internal.clone());
    let s16: [F; 16] = core::array::from_fn(|i| F::new(i as u32));
    let s24: [F; 24] = core::array::from_fn(|i| F::new(i as u32));
    assert_eq!(p16.permute(s16), q16.permute(s16), "width-16 constants");
    assert_eq!(p24.permute(s24), q24.permute(s24), "width-24 constants");
    (p16, p24, c16, c24)
}

/// The example's configuration on the Poseidon2 instances `p16`, `p24`.
pub fn config(p16: P16, p24: P24) -> ExampleConfig {
    let val_mmcs = ValMmcs::new(PaddingFreeSponge::new(p24.clone()), TruncatedPermutation::new(p16),
        3);
    let mut fri = FriParameters::new_benchmark_high_arity(ChallengeMmcs::new(val_mmcs.clone()));
    // `example_fri_parameters`: the fewest queries for 100 conjectured bits.
    fri.num_queries = (100 - fri.query_proof_of_work_bits).div_ceil(fri.log_blowup);
    while ConjecturedSecurity::compute_ldt_only(fri.log_blowup, fri.num_queries,
        fri.query_proof_of_work_bits, 128, EF::bits()).security_bits < 100
    {
        fri.num_queries += 1;
    }
    let pcs = TwoAdicFriPcs::new(Radix2DitParallel::default(), val_mmcs, fri);
    StarkConfig::new(pcs, DuplexChallenger::new(p24))
}

/// The inputs `generate_random_trace_rows` hashes: `n` draws of `SmallRng` seeded with `1`.
pub fn inputs(n: usize) -> Vec<[u64; 25]> {
    let mut rng = SmallRng::seed_from_u64(1);
    (0..n).map(|_| rng.random()).collect()
}

/// Canonical values, eight per line, each line indented by `indent`.
fn lean_lines(xs: &[F], indent: &str) -> String {
    xs.chunks(8)
        .map(|c| {
            let c: Vec<String> = c.iter().map(|x| x.as_canonical_u32().to_string()).collect();
            format!("{indent}{}", c.join(", "))
        })
        .collect::<Vec<_>>()
        .join(",\n")
}

fn lean_vectors<const W: usize>(rows: &[[F; W]]) -> String {
    rows.iter()
        .map(|r| format!("    #v[\n{}]", lean_lines(r, "      ")))
        .collect::<Vec<_>>()
        .join(",\n")
}

fn lean_list(xs: &[F]) -> String {
    format!("\n{}", lean_lines(xs, "    "))
}

/// `keccak-example-constants`: the Lean module of the example's Poseidon2 constants
/// (`fixtures/CompStarkFixtures/Poseidon2Example.lean`).
pub fn constants_module() {
    let (_, _, c16, c24) = poseidon2();
    println!("/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompStark.KoalaBear.Poseidon2

/-! # The Poseidon2 constants of Plonky3's example

The round constants `prove_prime_field_31` draws with `new_from_rng_128` from `SmallRng` seeded
with `1`, width 16 first, for its Poseidon2 Merkle commitment and challenger; generated by
`compstark-bench keccak-example-constants`. The instances are Plonky3's KoalaBear shape: the
S-box `x ^ 3`, four initial and four terminal full rounds, 20 and 23 partial rounds, KoalaBear's
internal diagonals (`instances`).
-/

namespace CompStark.Fixtures.Poseidon2Example

/-- The round constants of the initial full rounds at width 16. -/
def initial16 : List (Vector Nat 16) := [
{}]

/-- The round constants of the partial rounds at width 16. -/
def internal16 : List Nat := [{}]

/-- The round constants of the terminal full rounds at width 16. -/
def terminal16 : List (Vector Nat 16) := [
{}]

/-- The round constants of the initial full rounds at width 24. -/
def initial24 : List (Vector Nat 24) := [
{}]

/-- The round constants of the partial rounds at width 24. -/
def internal24 : List Nat := [{}]

/-- The round constants of the terminal full rounds at width 24. -/
def terminal24 : List (Vector Nat 24) := [
{}]

/-- The example's instances on KoalaBear's packed kernels. -/
def instances : CompStark.KoalaBear.Instances :=
  .ofNat initial16 internal16 terminal16 initial24 internal24 terminal24 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

end CompStark.Fixtures.Poseidon2Example",
        lean_vectors(&c16.initial), lean_list(&c16.internal), lean_vectors(&c16.terminal),
        lean_vectors(&c24.initial), lean_list(&c24.internal), lean_vectors(&c24.terminal));
}

/// `keccak-example L DIR`: the example's proof of `2^L / 24` Keccak-f permutations, after
/// Plonky3 verified it, as `DIR/keccak_example_L.json`, and the permutations' inputs as
/// `DIR/keccak_example_L_inputs.txt`, one input of 25 lanes per line. Prints the proof's postcard
/// size, the example's `Proof size`. Run with `RAYON_NUM_THREADS=1` for the smallest grinding
/// witnesses.
pub fn keccak_example(log_n: usize, dir: &str) {
    let (p16, p24, _, _) = poseidon2();
    let config = config(p16, p24);
    let air = KeccakAir {};
    let n = (1usize << log_n) / 24;
    let trace = air.generate_random_trace_rows::<F>(n, 1);
    let ins = inputs(n);
    assert_eq!(trace, p3_keccak_air::generate_trace_rows::<F>(ins.clone(), 1), "inputs");
    let proof = prove(&config, &air, trace, &[]).expect("Plonky3 cannot prove");
    verify(&config, &air, &proof, &[]).expect("Plonky3 rejects its own proof");
    println!("Proof size: {} bytes", postcard::to_allocvec(&proof).unwrap().len());
    std::fs::write(format!("{dir}/keccak_example_{log_n}.json"),
        serde_json::to_string(&proof).unwrap()).unwrap();
    let lines: String = ins.iter()
        .map(|i| i.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ") + "\n")
        .collect();
    std::fs::write(format!("{dir}/keccak_example_{log_n}_inputs.txt"), lines).unwrap();
}

/// `keccak-bench L REPS`: the example's trace generation, proof and verification of `2^L / 24`
/// permutations, `REPS` times; prints the median milliseconds of each.
pub fn keccak_bench(log_n: usize, reps: usize) {
    use std::time::Instant;
    let (p16, p24, _, _) = poseidon2();
    let config = config(p16, p24);
    let air = KeccakAir {};
    let n = (1usize << log_n) / 24;
    let (mut tg, mut tp, mut tv) = (vec![], vec![], vec![]);
    for _ in 0..reps {
        let t = Instant::now();
        let trace = air.generate_random_trace_rows::<F>(n, 1);
        tg.push(t.elapsed().as_secs_f64() * 1e3);
        let t = Instant::now();
        let proof = prove(&config, &air, trace, &[]).unwrap();
        tp.push(t.elapsed().as_secs_f64() * 1e3);
        let t = Instant::now();
        verify(&config, &air, &proof, &[]).unwrap();
        tv.push(t.elapsed().as_secs_f64() * 1e3);
    }
    let med = |v: &mut Vec<f64>| {
        v.sort_by(|a, b| a.partial_cmp(b).unwrap());
        v[v.len() / 2]
    };
    println!("plonky3 keccak 2^{log_n} tracegen {:.1} prove {:.1} verify {:.1} ms (median of {reps})",
        med(&mut tg), med(&mut tp), med(&mut tv));
}

/// `keccak-prove-trace L`: one round of `keccak-bench` with Plonky3's tracing spans printed, the
/// proof's phases.
pub fn keccak_prove_trace(log_n: usize) {
    use tracing_forest::util::LevelFilter;
    use tracing_forest::ForestLayer;
    use tracing_subscriber::layer::SubscriberExt;
    use tracing_subscriber::util::SubscriberInitExt;
    use tracing_subscriber::{EnvFilter, Registry};
    let env_filter = EnvFilter::builder().with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();
    Registry::default().with(env_filter).with(ForestLayer::default()).init();
    keccak_bench(log_n, 1);
}
