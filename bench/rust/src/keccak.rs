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

/// `lde LOG_N WIDTH`: the median milliseconds of five coset low-degree extensions by 2 of a
/// `2^LOG_N × WIDTH` matrix with `Radix2DitParallel`, as the commitment scheme extends a trace
/// (`coset_lde_batch` and the bit-reversal of the rows).
pub fn lde(log_n: usize, width: usize) {
    use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
    use p3_field::{Field, PrimeCharacteristicRing};
    use p3_matrix::bitrev::BitReversibleMatrix;
    use p3_matrix::dense::RowMajorMatrix;
    let n = 1 << log_n;
    let dft = Radix2DitParallel::<F>::default();
    let mut samples = vec![];
    for k in 0..6 {
        let m = RowMajorMatrix::new(
            (0..n * width).map(|i| F::from_u64((i as u64 * 2654435761 + k) % 2130706433)).collect(),
            width);
        let t = std::time::Instant::now();
        let ext = dft.coset_lde_batch(m, 1, F::GENERATOR).bit_reverse_rows().to_row_major_matrix();
        samples.push(t.elapsed().as_secs_f64() * 1e3);
        std::hint::black_box(ext);
    }
    samples.remove(0);
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("plonky3 lde 2^{log_n} x {width} ms median {:.1}", samples[2]);
}
