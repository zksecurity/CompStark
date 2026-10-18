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
    let perm24 = default_koalabear_poseidon2_24();
    let mut packed24 = vec![];
    for _ in 0..7 {
        let mut s: [P; 24] = core::array::from_fn(|i| P::from(F::from_u32(i as u32)));
        let t = Instant::now();
        for _ in 0..n / P::WIDTH { perm24.permute_mut(&mut s); }
        black_box(s);
        packed24.push(t.elapsed().as_nanos() as f64 / n as f64);
    }
    println!("plonky3 width24 ns/perm packed {:.1}", median(packed24));
}

/// Plonky3's Poseidon2 Merkle commitment to a `2^log_h × width` matrix with entries `7k + 1`:
/// the root and the median milliseconds of seven commits.
fn merkle(log_h: u32, width: usize) {
    use p3_commit::Mmcs;
    use p3_field::Field;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use std::time::Instant;
    type P = <F as Field>::Packing;
    let hash = PaddingFreeSponge::<_, 24, 16, 8>::new(default_koalabear_poseidon2_24());
    let compress = TruncatedPermutation::<_, 2, 8, 16>::new(default_koalabear_poseidon2_16());
    let mmcs = p3_merkle_tree::MerkleTreeMmcs::<P, P, _, _, 8>::new(hash, compress);
    let h = 1usize << log_h;
    let values: Vec<F> = (0..h * width).map(|k| F::from_u32(((7 * k as u64 + 1) % 2130706433) as u32)).collect();
    let m = RowMajorMatrix::new(values, width);
    let (root, _) = mmcs.commit(vec![m.clone()]);
    let root: Vec<u32> = root.into_iter().map(|x: F| x.as_canonical_u32()).collect();
    println!("root {:?}", root);
    let warm = Instant::now();
    while warm.elapsed().as_millis() < 200 {
        std::hint::black_box(mmcs.commit(vec![m.clone()]));
    }
    let mut samples = vec![];
    for _ in 0..15 {
        let input = m.clone();
        let t = Instant::now();
        let (root, tree) = mmcs.commit(vec![input]);
        samples.push(t.elapsed().as_secs_f64() * 1e3);
        std::hint::black_box((root, tree));
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("plonky3 merkle 2^{log_h} x {width} ms median {:.3}", samples[7]);
}

mod stark;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 4 && args[1] == "merkle" {
        return merkle(args[2].parse().unwrap(), args[3].parse().unwrap());
    }
    if args.len() == 2 && args[1] == "challenger" {
        return stark::challenger();
    }
    if args.len() >= 3 && args[1] == "prove-trace" {
        let nums: Vec<usize> = args[3..].iter().map(|a| a.parse().unwrap()).collect();
        return stark::prove_trace(&args[2], &nums);
    }
    if args.len() >= 3 && args[1] == "prove-bench" {
        let nums: Vec<usize> = args[3..].iter().map(|a| a.parse().unwrap()).collect();
        return stark::prove_bench(&args[2], &nums);
    }
    if args.len() >= 3 && args[1] == "stark" {
        let nums: Vec<usize> = args[3..].iter().map(|a| a.parse().unwrap()).collect();
        return stark::stark(&args[2], &nums);
    }
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
    // Merkle roots of matrices whose entry k is `base + k`.
    use p3_commit::Mmcs;
    use p3_field::Field;
    use p3_matrix::dense::RowMajorMatrix;
    type P = <F as Field>::Packing;
    let mmcs = p3_merkle_tree::MerkleTreeMmcs::<P, P, _, _, 8>::new(hash, compress);
    let mat = |base: u32, height: usize, width: usize| {
        RowMajorMatrix::new((0..(height * width) as u32).map(|k| F::from_u32(base + k)).collect(), width)
    };
    let cases: Vec<(&str, Vec<(u32, usize, usize)>)> = vec![
        ("single 8x3", vec![(0, 8, 3)]),
        ("single 5x2", vec![(0, 5, 2)]),
        ("single 1x10", vec![(0, 1, 10)]),
        ("multi", vec![(0, 4, 5), (1000, 8, 3), (2000, 2, 1), (3000, 1, 7), (4000, 8, 2)]),
        ("odd multi", vec![(0, 6, 3), (500, 3, 2)]),
    ];
    for (name, specs) in cases {
        let ms: Vec<_> = specs.iter().map(|&(b, h, w)| mat(b, h, w)).collect();
        let (root, _) = mmcs.commit(ms);
        let root: Vec<u32> = root.into_iter().map(|x: F| x.as_canonical_u32()).collect();
        println!("merkle {name} -> {:?}", root);
    }
}
