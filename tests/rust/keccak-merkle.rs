//! Read-only harness for leanMultisig 9d8bce818aa7c7e18e67026e522a9b1539d0a57d.
//! Link against the pinned checkout's unchanged production crates.
use fiat_shamir::FiatShamirState;
use pcs::merkle::MerkleBuilder;
use primitives::{field::{F64, F192}, hash};
use std::{hint::black_box, io::{BufRead, BufReader, Write}, time::Instant};

fn word(row: usize, col: usize) -> u64 {
    ((row as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15)) ^
        ((col as u64 + 17).wrapping_mul(0xd1b54a32d192ed03))
}
fn data(n: usize, width: usize) -> Vec<F64> {
    (0..n).flat_map(|r| (0..width).map(move |c| F64(word(r,c)))).collect()
}
fn commit(n: usize, width: usize, data: &[F64]) -> pcs::merkle::CutTree {
    let builder = MerkleBuilder::new(n, width, width);
    let tile = n.min(256);
    for first in (0..n).step_by(tile) {
        builder.absorb(first, &data[first*width..(first+tile)*width]);
    }
    builder.finish()
}
fn f(k: u64) -> F192 { F192::new(k, k ^ 0x1234, k.rotate_left(17)) }
fn fixtures() {
    print!("{{\"trees\":[");
    let mut first = true;
    for depth in [0,1,3,5] {
        let n = 1 << depth;
        for width in [1,8,16,17,34,64] {
            let rows = data(n, width);
            let tree = commit(n, width, &rows);
            for queries in [vec![n-1,0,n-1,n/2,1.min(n-1)], (0..n).rev().collect(), vec![n-1]] {
                let group_rows: Vec<F64> = tree.group_positions(&queries).into_iter()
                    .flat_map(|q| rows[q*width..(q+1)*width].iter().copied()).collect();
                let paths = tree.prune(&queries, width, width, &group_rows,
                    |q| &rows[q*width..(q+1)*width]);
                if !first { print!(","); }
                first = false;
                let images: Vec<Vec<u8>> = paths.leaf_data.iter().map(|row|
                    row.iter().flat_map(|x| x.0.to_le_bytes()).collect()).collect();
                print!("{{\"depth\":{depth},\"width\":{width},\"queries\":{queries:?},\"root\":{:?},\"siblings\":{:?},\"leaf_data\":{images:?}}}", tree.root(), paths.sibling_hashes);
            }
        }
    }
    print!("],\"duplex\":[");
    // Compare complete permutation checkpoints, and independently compare each sampled
    // scalar and carried capacity against the production FiatShamirState.
    let mut fs = FiatShamirState::new(std::array::from_fn(|i| F64(word(0,i))),
        std::array::from_fn(|i| F64(word(1,i))));
    let mut state = [0u64;25];
    for i in 0..8 { state[i] = word(i/4,i%4); }
    let event = |state: &mut [u64;25], initial: bool| {
        if !initial { print!(","); }
        print!("{{\"input\":{state:?},");
        hash::keccak_f(state);
        print!("\"output\":{state:?}}}");
        state[..16].fill(0);
    };
    event(&mut state, true);
    let mut pending = 0;
    for count in [0,1,4,5,8,9] {
        for k in 0..count {
            let x = f((count*100+k+1) as u64);
            fs.observe(x);
            if pending == 4 { event(&mut state, false); pending = 0; }
            state[4*pending..4*pending+4].copy_from_slice(&[x.c0,x.c1,x.c2,1]);
            pending += 1;
        }
        // The sample output is checked before clearing the rate.
        let expected = fs.sample();
        let mut output = state;
        hash::keccak_f(&mut output);
        assert_eq!([expected.c0,expected.c1,expected.c2], output[..3]);
        event(&mut state, false);
        pending = 0;
        let caps = fs.capacity_cells();
        assert_eq!(caps[0].c0, state[16]);
        for c in 1..5 { assert_eq!([caps[c].c0,caps[c].c1], state[15+2*c..17+2*c]); }
    }
    print!("],\"grinding\":[");
    for (i,bits) in [0,8,13].into_iter().enumerate() {
        if i > 0 { print!(","); }
        let mut probe = fs.clone();
        let nonce = probe.grind_pow(bits);
        let challenge = probe.sample();
        print!("{{\"bits\":{bits},\"nonce\":{nonce},\"challenge\":[{},{},{}]}}",challenge.c0,challenge.c1,challenge.c2);
    }
    println!("]}}");
}
fn run(mut mark: impl FnMut(&str)) {
    let mut state = [0u64;25];
    state[0] = 0x123456789abcdef0;
    mark("begin");
    for _ in 0..10000 { hash::keccak_f(black_box(&mut state)); }
    mark("end f1600 native");
    assert_eq!(state[0], 0x03d0008026579d6c);
    let (n,width) = (4096,64);
    let rows = data(n,width);
    mark("begin");
    let t = Instant::now();
    let tree = commit(n,width,black_box(&rows));
    let ns = t.elapsed().as_nanos();
    mark("end commit");
    println!("commit ns={ns} root={:?}",tree.root());
    let queries: Vec<usize> = (0..100).map(|i| (i*197+23)%n).collect();
    let group_rows: Vec<F64> = tree.group_positions(&queries).into_iter()
        .flat_map(|q| rows[q*width..(q+1)*width].iter().copied()).collect();
    mark("begin");
    let t = Instant::now();
    let opening = tree.prune(black_box(&queries),width,width,&group_rows,
        |q| &rows[q*width..(q+1)*width]);
    let ns = t.elapsed().as_nanos();
    mark("end open");
    println!("open ns={ns} rows={} siblings={} sink={:?}",opening.leaf_data.len(),opening.sibling_hashes.len(),opening.sibling_hashes[0]);
    let mut fs = fiat_shamir::transcript::ProverState::new(std::array::from_fn(|i| F64(word(0,i))),
        std::array::from_fn(|i| F64(word(1,i))));
    let mut sink = 0u64;
    mark("begin");
    let t = Instant::now();
    for i in 0..10000 { fs.add_scalar(f(i)); sink = sink.wrapping_add(fs.sample().c0); }
    let ns = t.elapsed().as_nanos();
    mark("end duplex");
    assert_eq!(fs.into_proof().stream.len(),10000);
    println!("duplex ns={ns} sink={sink}");
    let mut fs = FiatShamirState::new(std::array::from_fn(|i| F64(word(0,i))),
        std::array::from_fn(|i| F64(word(1,i))));
    mark("begin");
    let t = Instant::now();
    let nonce = fs.grind_pow(8);
    let ns = t.elapsed().as_nanos();
    mark("end grind");
    println!("grind ns={ns} nonce={nonce}");
}
fn run_grind20(mut mark: impl FnMut(&str)) {
    let mut fs = FiatShamirState::new(std::array::from_fn(|i| F64(word(0,i))),
        std::array::from_fn(|i| F64(word(1,i))));
    mark("begin");
    let nonce = fs.grind_pow(20);
    mark("end grind20");
    assert_eq!(nonce, 124138);
    let c = fs.sample();
    assert_eq!([c.c0,c.c1,c.c2], [5366933390071687144,3650987668691482591,2331228947711704332]);
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("fixtures") => fixtures(),
        Some("grind") => {
            let mut fs = FiatShamirState::new(std::array::from_fn(|i| F64(word(0,i))),
                std::array::from_fn(|i| F64(word(1,i))));
            let t = Instant::now();
            let nonce = fs.grind_pow(20);
            let ns = t.elapsed().as_nanos();
            let c = fs.sample();
            println!("grind ns={ns} nonce={nonce} challenge={:?}", [c.c0,c.c1,c.c2]);
        },
        Some("gate") => {
            let mut ctl = std::fs::OpenOptions::new().write(true).open(format!("{}/ctl",args.last().unwrap())).unwrap();
            let mut ack = BufReader::new(std::fs::File::open(format!("{}/ack",args.last().unwrap())).unwrap());
            let mark = |msg: &str| { writeln!(ctl,"{msg}").unwrap(); ctl.flush().unwrap(); let mut line=String::new(); ack.read_line(&mut line).unwrap(); };
            if args.get(2).is_some_and(|s| s == "keccak-grind") { run_grind20(mark); } else { run(mark); }
        },
        Some("bench") => run(|_| {}),
        _ => panic!("usage: keccak-merkle-reference fixtures|bench|gate DIR"),
    }
}
