// Copyright (c) 2026 zkSecurity. Apache-2.0.
// Read-only harness for leanMultisig 9d8bce818aa7c7e18e67026e522a9b1539d0a57d, compiled as a
// child of the unchanged `keccak_gkr` crate by `scripts/check-binary-stack-reference`.
// Arguments: an output directory and the committed Keccak region (`committed.bin`, 64
// column-major lanes of little-endian words). Writes every sliced witness layer, the batch
// point and output claims, the transmitted stream, every layer's batched claim, every
// challenge and both terminal openings of the two-segment GKR reduction.
use crate::{OutputClaim, Shape, Witness};
use fiat_shamir::transcript::ProverState;
use primitives::field::{F64, F192};
use std::path::Path;

fn dump(path: &Path, data: impl IntoIterator<Item=u64>) {
    std::fs::write(path, data.into_iter().flat_map(u64::to_le_bytes).collect::<Vec<_>>()).unwrap();
}
fn limbs(xs: &[F192]) -> impl Iterator<Item=u64> + '_ { xs.iter().flat_map(|e| [e.c0,e.c1,e.c2]) }

pub fn run() {
    let args: Vec<_> = std::env::args().collect();
    let out = Path::new(&args[1]);
    std::fs::create_dir_all(out).unwrap();
    let bytes = std::fs::read(&args[2]).unwrap();
    assert_eq!(bytes.len() % (64*8), 0);
    let committed: Vec<_> = bytes.chunks_exact(8).map(|b| F64(u64::from_le_bytes(b.try_into().unwrap()))).collect();
    let n = committed.len()/64;
    let inputs: Vec<[u64;25]> = (0..n).map(|i| std::array::from_fn(|l| committed[l*n+i].0)).collect();
    let shape = Shape::new(n,12);
    assert_eq!(shape.n(), n);
    let mut expected = vec![F64::ZERO; committed.len()];
    let witness = Witness::generate(shape, &inputs, &mut expected);
    assert_eq!(expected[..50*n], committed[..50*n]);
    for r in 0..=24 {
        dump(&out.join(format!("layer-{r}.bin")), (0..shape.n_blocks()).flat_map(|g| witness.layer(r,g).iter().copied()));
    }
    let mut ps = ProverState::new([F64(1),F64(2),F64(3),F64(4)], [F64(5),F64(6),F64(7),F64(8)]);
    let instance = ps.sample_vec(shape.n_log());
    let output = OutputClaim::of_inputs(shape, &inputs, instance.clone());
    // The caller binds its public output claim before entering the reduction.
    ps.add_scalars(&output.lanes);
    dump(&out.join("instance.bin"), limbs(&instance));
    dump(&out.join("output.bin"), limbs(&output.lanes));
    let openings = witness.prove(&mut ps, &committed, &output);
    let proof = ps.into_proof();
    dump(&out.join("stream.bin"), limbs(&proof.stream));
    let outputs = openings.outputs.unwrap();
    dump(&out.join("word-point.bin"), limbs(&outputs.point));
    dump(&out.join("word-value.bin"), limbs(&[outputs.value]));
    dump(&out.join("slice-point.bin"), limbs(&openings.inputs.point));
    dump(&out.join("slices.bin"), limbs(&openings.inputs.slices));
    // Re-run the original layer entry point to expose all batched claims.
    let mut replay = ProverState::new([F64(1),F64(2),F64(3),F64(4)], [F64(5),F64(6),F64(7),F64(8)]);
    assert_eq!(replay.sample_vec(shape.n_log()), instance);
    replay.add_scalars(&output.lanes);
    let segment = replay.sample_vec(shape.seg_log());
    let lane_point = replay.sample_vec(crate::keccak::LANE_VARS);
    let mut claim = crate::first(shape, &output, segment, &lane_point);
    let (_, middle) = crate::open::output_claim(shape, &committed, &instance, &claim);
    replay.add_scalar(middle);
    claim.value += middle;
    let mut scratch = crate::prover::Scratch::new(shape);
    for step in 0..shape.depth {
        claim = crate::prover::prove_layer(&mut replay, &witness, &mut scratch, step, &claim);
        let cells: Vec<_> = std::iter::once(claim.value).chain(claim.mu.iter().copied())
            .chain(claim.point.iter().copied()).chain(claim.weights.iter().copied()).collect();
        dump(&out.join(format!("claim-{step}.bin")), limbs(&cells));
    }
    assert!(proof.stream.starts_with(&replay.into_proof().stream));
    // Replay the transcript independently, retaining every sampled challenge.
    let mut fs = fiat_shamir::FiatShamirState::new([F64(1),F64(2),F64(3),F64(4)], [F64(5),F64(6),F64(7),F64(8)]);
    let mut challenges = fs.sample_vec(shape.n_log());
    assert_eq!(challenges, instance);
    let mut at=0;
    fn absorb(fs:&mut fiat_shamir::FiatShamirState, stream:&[F192], at:&mut usize, count:usize) {
        for &x in &stream[*at..*at+count] { fs.observe(x); } *at+=count;
    }
    absorb(&mut fs,&proof.stream,&mut at,25);
    challenges.extend(fs.sample_vec(6));
    absorb(&mut fs,&proof.stream,&mut at,1);
    for _ in 0..12 {
        absorb(&mut fs,&proof.stream,&mut at,47); challenges.push(fs.sample());
        for _ in 0..shape.y_vars() { absorb(&mut fs,&proof.stream,&mut at,2); challenges.push(fs.sample()); }
        for _ in 0..11 { absorb(&mut fs,&proof.stream,&mut at,3); challenges.push(fs.sample()); }
        absorb(&mut fs,&proof.stream,&mut at,3); challenges.push(fs.sample());
    }
    for _ in 0..6 { absorb(&mut fs,&proof.stream,&mut at,2); challenges.push(fs.sample()); }
    absorb(&mut fs,&proof.stream,&mut at,1);
    for _ in 0..10 { absorb(&mut fs,&proof.stream,&mut at,2); challenges.push(fs.sample()); }
    absorb(&mut fs,&proof.stream,&mut at,64);
    assert_eq!(at,proof.stream.len());
    dump(&out.join("challenges.bin"), limbs(&challenges));
}
