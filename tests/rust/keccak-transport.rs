// Copyright (c) 2026 zkSecurity. Apache-2.0.
//! Read-only harness for leanMultisig 9d8bce818aa7c7e18e67026e522a9b1539d0a57d, linked against
//! its unchanged `pcs`, `fiat_shamir` and `primitives` crates by
//! `scripts/check-binary-stack-reference`. Argument: an output directory. Writes the smallest
//! grinding nonce and the following challenge at 0, 5 and 9 bits after seven transmitted
//! scalars, and the root, opened rows and pruned sibling hashes of a sixteen-leaf Keccak Merkle
//! tree of three-word rows at queries `[9, 3, 9, 0, 15, 8]`.
use fiat_shamir::transcript::ProverState;
use primitives::field::{F64, F192};
use std::{fs, path::Path};
fn value(i: u64) -> F192 {
    F192::new(0x123456789abcdef0u64.wrapping_add(31 * i),
        0xfedcba9876543210u64.wrapping_add(i * i),
        0x8000000000000001u64.wrapping_add(17 * i))
}
fn main() {
    let output = std::path::PathBuf::from(std::env::args().nth(1).unwrap());
    let output: &Path = &output;
    fs::create_dir_all(output).unwrap();
    for bits in [0u32, 5, 9] {
        let mut ps = ProverState::new([F64(1), F64(2), F64(3), F64(4)],
            [F64(5), F64(6), F64(7), F64(8)]);
        ps.add_scalars(&(0..7).map(value).collect::<Vec<_>>());
        ps.grind(bits);
        let next = ps.sample();
        let proof = ps.into_proof();
        let nonce = *proof.stream.last().unwrap();
        fs::write(output.join(format!("grind-{bits}.bin")),
            [nonce, next].iter().flat_map(|x| [x.c0, x.c1, x.c2])
                .flat_map(u64::to_le_bytes).collect::<Vec<_>>()).unwrap();
    }
    let rows: Vec<F64> = (0..16).flat_map(|i| (0..3).rev().map(move |j| F64(31*i+j+1))).collect();
    let builder = pcs::merkle::MerkleBuilder::new(16, 3, 8);
    builder.absorb(0, &rows);
    let tree = builder.finish();
    let queries = [9usize, 3, 9, 0, 15, 8];
    let group_rows: Vec<_> = tree.group_positions(&queries).iter()
        .flat_map(|&q| rows[3*q..3*q+3].iter().copied()).collect();
    let opening = tree.prune(&queries, 3, 8, &group_rows, |q| &rows[3*q..3*q+3]);
    fs::write(output.join("merkle-root.bin"), tree.root()).unwrap();
    fs::write(output.join("merkle-rows.bin"), opening.leaf_data.iter().flatten()
        .flat_map(|w| w.0.to_le_bytes()).collect::<Vec<_>>()).unwrap();
    fs::write(output.join("merkle-hashes.bin"), opening.sibling_hashes.iter().flatten().copied().collect::<Vec<_>>()).unwrap();
}
