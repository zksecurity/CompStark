//! Plonky3's `KeccakAir`: known answers of its trace generator.
use p3_field::PrimeField32;
use p3_koala_bear::{default_koalabear_poseidon2_24, KoalaBear};
use p3_matrix::Matrix;
use p3_symmetric::{CryptographicHasher, PaddingFreeSponge};

type F = KoalaBear;

/// The fixed inputs of the trace known answers: lane `i` of input `k` is
/// `(25 k + i + 1) · 0x9e3779b97f4a7c15`, wrapping.
pub fn kat_inputs(count: usize) -> Vec<[u64; 25]> {
    (0..count)
        .map(|k| core::array::from_fn(|i| ((25 * k + i + 1) as u64).wrapping_mul(0x9e3779b97f4a7c15)))
        .collect()
}

/// `keccak-trace INPUTS`: the trace of `generate_trace_rows` on `kat_inputs(INPUTS)`, one line per
/// row: the row's digest by Plonky3's Poseidon2 sponge (`PaddingFreeSponge<_, 24, 16, 8>`).
pub fn trace_kat(count: usize) {
    let trace = p3_keccak_air::generate_trace_rows::<F>(kat_inputs(count), 0);
    let sponge = PaddingFreeSponge::<_, 24, 16, 8>::new(default_koalabear_poseidon2_24());
    for r in 0..trace.height() {
        let row = trace.row_slice(r).unwrap();
        let d: [F; 8] = sponge.hash_iter(row.iter().copied());
        let d: Vec<String> = d.iter().map(|x| x.as_canonical_u32().to_string()).collect();
        println!("{}", d.join(" "));
    }
}
