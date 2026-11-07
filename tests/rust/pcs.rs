// Copyright (c) 2026 zkSecurity. Apache-2.0.
// External driver of the unchanged leanMultisig binary-field PCS kernels.
use primitives::field::{F64, F192};
use std::{fs, io::{BufRead, Write}, path::Path};
fn value(i: u64) -> F192 {
    F192::new(0x123456789abcdef0u64.wrapping_add(31 * i),
        0xfedcba9876543210u64.wrapping_add(i * i),
        0x8000000000000001u64.wrapping_add(17 * i))
}
type Marks = Option<(fs::File, std::io::BufReader<fs::File>)>;
fn mark(marks: &mut Marks, command: &str) {
    if let Some((ctl, ack)) = marks {
        writeln!(ctl, "{command}").unwrap(); ctl.flush().unwrap();
        let mut line = String::new(); ack.read_line(&mut line).unwrap();
        assert_eq!(line.trim(), "ok");
    }
}
fn bytes(values: &[F192]) -> Vec<u8> {
    values.iter().flat_map(|x| [x.c0, x.c1, x.c2]).flat_map(u64::to_le_bytes).collect()
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let fixture = args[1] == "fixture";
    let directory = if args.get(1).map(String::as_str) == Some("gate") { Some(Path::new(&args[3])) } else { None };
    let mut marks = directory.map(|d| (fs::OpenOptions::new().write(true).open(d.join("ctl")).unwrap(),
        std::io::BufReader::new(fs::OpenOptions::new().read(true).open(d.join("ack")).unwrap())));
    let challenges = std::array::from_fn(|i| value(i as u64 + 19));
    mark(&mut marks, "begin");
    let started = std::time::Instant::now();
    let coordinates = pcs::ring_switch::build_coordinate_weights(&challenges);
    std::hint::black_box(&coordinates);
    let coordinate_ns = started.elapsed().as_nanos();
    mark(&mut marks, "end coordinates");
    let point: Vec<_> = (0..8).map(|i| value(i + 101)).collect();
    let tensor = pcs::whir::build_eq_table_ext(&point);
    let packed: Vec<_> = (0..256).map(|i| F64(0x9e3779b97f4a7c15u64.wrapping_mul(i + 1))).collect();
    mark(&mut marks, "begin");
    let started = std::time::Instant::now();
    let slices = pcs::ring_switch::fold_1b_rows(&packed, &tensor);
    std::hint::black_box(&slices);
    let fold_ns = started.elapsed().as_nanos();
    mark(&mut marks, "end bit-fold");
    mark(&mut marks, "begin");
    let started = std::time::Instant::now();
    let mapped: Vec<_> = tensor.iter().map(|x| {
        let mut acc = F192::ZERO;
        for (limb, word) in [x.c0, x.c1, x.c2].into_iter().enumerate() {
            let mut bits = word;
            while bits != 0 {
                acc += coordinates[64 * limb + bits.trailing_zeros() as usize];
                bits &= bits - 1;
            }
        }
        acc
    }).collect();
    std::hint::black_box(&mapped);
    let basis_ns = started.elapsed().as_nanos();
    mark(&mut marks, "end basis");
    if fixture {
        let d = Path::new(&args[2]); fs::create_dir_all(d).unwrap();
        for (name, values) in [("coordinates", coordinates.as_slice()), ("tensor", &tensor), ("slices", &slices), ("mapped", &mapped)] {
            fs::write(d.join(format!("{name}.bin")), bytes(values)).unwrap();
        }
    }
    println!("nanoseconds coordinates={coordinate_ns} bit-fold={fold_ns} basis={basis_ns}");
    println!("coordinates={} sink={} slices={}", coordinates.len(), coordinates[191].c0, slices[63].c0);
}
