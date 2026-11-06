//! Kernel comparison for `CompStarkBench keccak-kernels N`.
use p3_keccak::{Keccak256Hash, KeccakF};
use p3_symmetric::{CryptographicHasher, Permutation};
use std::hint::black_box;
use std::time::Instant;

fn lane(h: [u8; 32]) -> u64 {
    u64::from_le_bytes(h[..8].try_into().unwrap())
}

fn run(n: usize, mut mark: impl FnMut(&str)) {
    assert!(n > 0);
    let mut state = [0u64; 25];
    state[0] = 0x123456789abcdef0;
    mark("begin");
    let t = Instant::now();
    for _ in 0..n {
        KeccakF.permute_mut(black_box(&mut state));
    }
    let ns = t.elapsed().as_nanos();
    mark("end f1600 chain");
    println!("f1600 n={n} ns/op={} sink={}", ns / n as u128, state[0]);
    if n == 10000 {
        assert_eq!(state[0], 0x03d0008026579d6c);
    }
    for len in [64, 512] {
        let input: Vec<u8> = (0..len).map(|i| i as u8).collect();
        let mut sink = 0u64;
        mark("begin");
        let t = Instant::now();
        for _ in 0..n {
            sink = sink.wrapping_add(lane(black_box(
                Keccak256Hash.hash_iter_slices([black_box(input.as_slice())]),
            )));
        }
        let ns = t.elapsed().as_nanos();
        mark(&format!("end hash {len}"));
        println!(
            "keccak256 len={len} n={n} ns/op={} sink={sink}",
            ns / n as u128
        );
    }
    let rounds = n.div_ceil(1024);
    let count = rounds * 1024;
    let mut states: Vec<[u64; 25]> = (0..1024)
        .map(|j| {
            std::array::from_fn(|i| ((j * 25 + i + 1) as u64).wrapping_mul(0x9e3779b97f4a7c15))
        })
        .collect();
    mark("begin");
    let t = Instant::now();
    for _ in 0..rounds {
        for state in &mut states {
            KeccakF.permute_mut(black_box(state));
        }
    }
    let ns = t.elapsed().as_nanos();
    mark("end f1600 batch");
    let sink = states.iter().fold(0u64, |s, st| s.wrapping_add(st[0]));
    println!(
        "f1600 batch n={count} ns/op={} sink={sink}",
        ns / count as u128
    );
    for len in [64, 512] {
        let input: Vec<u8> = (0..len * 1024).map(|i| i as u8).collect();
        let mut output = vec![[0u8; 32]; 1024];
        let mut sink = 0u64;
        mark("begin");
        let t = Instant::now();
        for _ in 0..rounds {
            Keccak256Hash.hash_many(black_box(&input), black_box(&mut output));
            sink = output.iter().fold(sink, |s, h| s.wrapping_add(lane(*h)));
        }
        let ns = t.elapsed().as_nanos();
        mark(&format!("end batch hash {len}"));
        println!(
            "keccak256 batch len={len} n={count} max_compiled_lanes={} ns/op={} sink={sink}",
            <Keccak256Hash as CryptographicHasher<u8, [u8; 32]>>::LANES,
            ns / count as u128
        );
    }
}

/// Wall-clock run, with an empty phase marker compiled away.
pub fn kernels(n: usize) {
    run(n, |_| {});
}

/// Instruction-count run using the same acknowledged FIFO protocol as Lean's gate.
pub fn gate(dir: &str) {
    use std::fs::OpenOptions;
    use std::io::{BufRead, BufReader, Write};
    use std::path::Path;
    let mut ctl = OpenOptions::new()
        .write(true)
        .open(Path::new(dir).join("ctl"))
        .unwrap();
    let mut ack = BufReader::new(
        OpenOptions::new()
            .read(true)
            .open(Path::new(dir).join("ack"))
            .unwrap(),
    );
    run(10000, |msg| {
        writeln!(ctl, "{msg}").unwrap();
        ctl.flush().unwrap();
        let mut line = String::new();
        ack.read_line(&mut line).unwrap();
        assert_eq!(line, "ok\n");
    });
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 4 && args[1] == "gate" && args[2] == "keccak-kernels" {
        gate(&args[3]);
    } else if args.len() == 2 {
        kernels(args[1].parse().unwrap());
    } else {
        panic!("usage: keccak-kernels N | gate keccak-kernels DIR");
    }
}
