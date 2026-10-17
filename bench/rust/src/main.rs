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

fn main() {
    let p16 = default_koalabear_poseidon2_16();
    let p24 = default_koalabear_poseidon2_24();
    show("w16 zero", [0u32; 16], &p16);
    show("w16 iota", core::array::from_fn::<u32, 16, _>(|i| i as u32), &p16);
    show("w16 sage", [894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
        120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920,
        1783754913], &p16);
    show("w24 zero", [0u32; 24], &p24);
    show("w24 iota", core::array::from_fn::<u32, 24, _>(|i| i as u32), &p24);
}
