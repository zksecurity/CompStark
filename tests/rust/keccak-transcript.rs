// Copyright (c) 2026 zkSecurity. Apache-2.0.
// Read-only harness for leanMultisig 9d8bce818aa7c7e18e67026e522a9b1539d0a57d, compiled with
// the unchanged modules of its `verifier` crate by `scripts/check-binary-stack-reference`.
// Prints the transcript seed, squeezes across rate boundaries, digest absorption, grinding,
// repeated zero absorptions, leaf hashes and a pruned Merkle multi-opening.
use field::{E, K};
use hash::{Digest, keccak_hash};
use transcript::{Proof, Sponge, Transcript};
use merkle::{MerkleOpenings, PrunedMerklePaths};

fn e(x: E) -> String { format!("[{}, {}, {}]", x.c0, x.c1, x.c2) }
fn hex(x: Digest) -> String { x.0.iter().map(|b| format!("{b:02x}")).collect() }
fn f(k: u64) -> E { E::new(k, k ^ 0x1234, k.rotate_left(17)) }
fn main() {
    let iv = keccak_hash(b"leanvm-v1\x00\x01\x02\xff");
    let public_input = Digest(std::array::from_fn(|i| i as u8));
    println!("iv {}", hex(iv));
    for n in [0, 1, 3, 4, 5, 8, 9] {
        let mut sp = Sponge::new(iv, public_input);
        for k in 0..n { sp.observe(f(k + 1)); }
        println!("draw {n} {} {}", e(sp.sample()), e(sp.sample()));
    }
    let (lo, hi) = public_input.halves();
    let mut sp = Sponge::new(iv, public_input);
    sp.observe(lo); sp.observe(hi);
    println!("digest {}", e(sp.sample()));
    for bits in [0, 8] {
        let nonce = (0..).find(|&n| {
            let proof = Proof { stream: vec![f(7), E::new(n,0,0)], merkle_openings: MerkleOpenings::Pruned(vec![]) };
            let mut tr = Transcript::new(&proof, iv, public_input, true);
            tr.next_scalar().unwrap();
            tr.grind_check(bits).is_ok()
        }).unwrap();
        let proof = Proof { stream: vec![f(7), E::new(nonce,0,0)], merkle_openings: MerkleOpenings::Pruned(vec![]) };
        let mut tr = Transcript::new(&proof, iv, public_input, true);
        tr.next_scalar().unwrap(); tr.grind_check(bits).unwrap();
        println!("grind {bits} {nonce} {}", e(tr.sample()));
    }
    for n in [0, 1, 4, 5, 8, 9] {
        let mut sp = Sponge::new(iv, public_input);
        for _ in 0..n { sp.observe(E::new(0,0,0)); }
        println!("zero {n} {}", e(sp.sample()));
    }
    for prefix in [0, 1, 17, 18, 34] {
        let leaf: Vec<u8> = vec![K(0); prefix].into_iter().chain([K(1), K(0x0807060504030201)]).flat_map(K::to_bytes).collect();
        println!("leaf {prefix} {}", hex(keccak_hash(&leaf)));
    }
    let image = |p: u64| -> Vec<K> { vec![K(0), K(4*p+1), K(4*p+2), K(4*p+3)] };
    let mut levels = vec![(0..8).map(|p| keccak_hash(&image(p).into_iter().flat_map(K::to_bytes).collect::<Vec<_>>())).collect::<Vec<_>>()];
    for j in 0..3 {
        let parents = levels[j].chunks_exact(2).map(|pair| merkle::hash_pair(&pair[0].0,&pair[1].0)).collect();
        levels.push(parents);
    }
    let batch = PrunedMerklePaths {
        leaf_data: [1,4,5].into_iter().map(|p| image(p)[1..].to_vec()).collect(),
        sibling_hashes: vec![levels[0][0].0,levels[1][1].0,levels[1][3].0]
    };
    let (root, paths) = batch.expand(3, &[5,1,5,4],3,4).unwrap();
    println!("root {}",hex(root));
    for h in &batch.sibling_hashes { println!("hint {}",hex(Digest(*h))); }
    for p in paths {
        assert_eq!(p.root(),root);
        println!("path {} {}",p.leaf_index,p.siblings.iter().map(|h|hex(Digest(*h))).collect::<Vec<_>>().join(" "));
    }
}
