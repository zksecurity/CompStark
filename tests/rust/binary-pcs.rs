// Copyright (c) 2026 zkSecurity. Apache-2.0.
//! Read-only harness for leanMultisig 9d8bce818aa7c7e18e67026e522a9b1539d0a57d, linked against
//! its unchanged `pcs` and `primitives` crates by `scripts/check-binary-stack-reference`.
//! Arguments: the packed base-field region (`tests/data/keccak-gkr/active/committed.bin`) and an
//! output directory. Writes the 64 ring-switching bit-slice values at a fixed point, the
//! six-map ring-switching target, and the inverse-rate-four additive encoding of 1,024
//! extension values in 64 rows of 16 lanes.
use primitives::field::{F64, F192};
use std::{fs, path::Path};
fn value(i: u64) -> F192 {
    F192::new(0x123456789abcdef0u64.wrapping_add(31 * i),
        0xfedcba9876543210u64.wrapping_add(i * i),
        0x8000000000000001u64.wrapping_add(17 * i))
}
fn bytes(values: &[F192]) -> Vec<u8> {
    values.iter().flat_map(|x| [x.c0, x.c1, x.c2]).flat_map(u64::to_le_bytes).collect()
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let packed_bytes = fs::read(&args[1]).unwrap();
    assert_eq!(packed_bytes.len(), 8 * (1 << 15));
    let packed: Vec<_> = packed_bytes.chunks_exact(8).map(|b| F64(u64::from_le_bytes(b.try_into().unwrap()))).collect();
    let point: Vec<_> = (0..15).map(|i| value(i + 101)).collect();
    let tensor = pcs::whir::build_eq_table_ext(&point);
    let slices = pcs::ring_switch::fold_1b_rows(&packed, &tensor);
    let challenges = std::array::from_fn(|i| value(i as u64 + 19));
    let coordinates = pcs::ring_switch::build_coordinate_weights(&challenges);
    let mut target = F192::ZERO;
    for (i, x) in slices.iter().enumerate() {
        let mut mapped = F192::ZERO;
        for (limb, word) in [x.c0, x.c1, x.c2].into_iter().enumerate() {
            let mut bits = word;
            while bits != 0 {
                mapped += coordinates[64 * limb + bits.trailing_zeros() as usize];
                bits &= bits - 1;
            }
        }
        target += mapped * F192::new(1u64 << i, 0, 0);
    }
    let message: Vec<_> = (0..1024).map(value).flat_map(|x| [F64(x.c0), F64(x.c1), F64(x.c2)]).collect();
    let ntt = pcs::ntt::AdditiveNttF64::standard(8);
    let pcs::ntt::Codeword::Whole(encoded, _) = ntt.encode_interleaved_with(&message, 48, 2, false, &|_, _| {}) else { panic!("full codeword required") };
    let output = Path::new(&args[2]);
    fs::create_dir_all(output).unwrap();
    fs::write(output.join("encoded.bin"), encoded.iter().flat_map(|x| x.0.to_le_bytes()).collect::<Vec<_>>()).unwrap();
    fs::write(output.join("ring-slices.bin"), bytes(&slices)).unwrap();
    fs::write(output.join("ring-target.bin"), bytes(&[target])).unwrap();
}
