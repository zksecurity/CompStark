//! Known answers for Plonky3's default KoalaBear Poseidon2 permutations.
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::{default_koalabear_poseidon2_16, default_koalabear_poseidon2_24, KoalaBear as F};
use p3_symmetric::Permutation;

fn show<const W: usize>(label: &str, input: [u32; W], perm: &impl Permutation<[F; W]>) {
    let mut state = input.map(F::from_u32);
    perm.permute_mut(&mut state);
    let out: Vec<u32> = state.iter().map(|x| x.as_canonical_u32()).collect();
    println!("{label} {:?}\n  -> {:?}", input, out);
}

/// Median nanoseconds per permutation, single thread: scalar chained states, and AVX2-packed
/// states (eight lanes per `PackedKoalaBear`).
fn bench(log_n: u32) {
    use p3_field::{Field, PackedValue};
    use std::hint::black_box;
    use std::time::Instant;
    type P = <F as Field>::Packing;
    let perm = default_koalabear_poseidon2_16();
    let n = 1usize << log_n;
    let median = |mut v: Vec<f64>| { v.sort_by(|a, b| a.partial_cmp(b).unwrap()); v[v.len() / 2] };
    let mut scalar = vec![];
    let mut packed = vec![];
    for _ in 0..7 {
        let mut s: [F; 16] = core::array::from_fn(|i| F::from_u32(i as u32));
        let t = Instant::now();
        for _ in 0..n { perm.permute_mut(&mut s); }
        black_box(s);
        scalar.push(t.elapsed().as_nanos() as f64 / n as f64);
        let mut s: [P; 16] = core::array::from_fn(|i| P::from(F::from_u32(i as u32)));
        let t = Instant::now();
        for _ in 0..n / P::WIDTH { perm.permute_mut(&mut s); }
        black_box(s);
        packed.push(t.elapsed().as_nanos() as f64 / n as f64);
    }
    println!("plonky3 width16 ns/perm scalar {:.1} packed({} lanes) {:.1}", median(scalar), P::WIDTH, median(packed));
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 3 && args[1] == "bench" {
        return bench(args[2].parse().unwrap());
    }
    let p16 = default_koalabear_poseidon2_16();
    let p24 = default_koalabear_poseidon2_24();
    show("w16 zero", [0u32; 16], &p16);
    show("w16 iota", core::array::from_fn::<u32, 16, _>(|i| i as u32), &p16);
    show("w16 sage", [894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
        120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920,
        1783754913], &p16);
    show("w24 zero", [0u32; 24], &p24);
    show("w24 iota", core::array::from_fn::<u32, 24, _>(|i| i as u32), &p24);
    // Plonky3's Poseidon2 Merkle hash and compression (`examples/src/types.rs`).
    use p3_symmetric::{CryptographicHasher, PaddingFreeSponge, PseudoCompressionFunction,
        TruncatedPermutation};
    let hash = PaddingFreeSponge::<_, 24, 16, 8>::new(p24.clone());
    let compress = TruncatedPermutation::<_, 2, 8, 16>::new(p16.clone());
    for n in [0u32, 1, 8, 16, 17, 32, 50] {
        let out: [F; 8] = hash.hash_iter((0..n).map(F::from_u32));
        let out: Vec<u32> = out.iter().map(|x| x.as_canonical_u32()).collect();
        println!("sponge iota {n} -> {:?}", out);
    }
    let a: [F; 8] = core::array::from_fn(|i| F::from_u32(i as u32));
    let b: [F; 8] = core::array::from_fn(|i| F::from_u32(100 + i as u32));
    let out: Vec<u32> = compress.compress([a, b]).iter().map(|x| x.as_canonical_u32()).collect();
    println!("compress iota/100 -> {:?}", out);
}
