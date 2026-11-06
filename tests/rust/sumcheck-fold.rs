// Copyright (c) 2026 zkSecurity. Apache-2.0.
// External driver of the unchanged leanMultisig cubic-extension interpolation.
use primitives::{field::F192, multilinear::interp};
use std::{fs, io::Write, path::Path};
fn value(i: u64) -> F192 {
    F192::new(0x123456789abcdef0u64.wrapping_add(31 * i),
        0xfedcba9876543210u64.wrapping_add(i * i),
        0x8000000000000001u64.wrapping_add(17 * i))
}
fn mark(directory: &Path, command: &str) {
    let mut ctl = fs::OpenOptions::new().write(true).open(directory.join("ctl")).unwrap();
    let ack = fs::OpenOptions::new().read(true).open(directory.join("ack")).unwrap();
    writeln!(ctl, "{command}").unwrap();
    ctl.flush().unwrap();
    let mut reader = std::io::BufReader::new(ack);
    let mut line = String::new();
    std::io::BufRead::read_line(&mut reader, &mut line).unwrap();
    assert_eq!(line.trim(), "ok");
}
fn fold(rows: usize, width: usize, directory: Option<&Path>) -> Vec<F192> {
    let input: Vec<_> = (0..2 * rows * width).map(|i| value(i as u64)).collect();
    let r = value(19);
    if let Some(d) = directory { mark(d, "begin"); }
    let output: Vec<_> = (0..rows * width).map(|i| {
        let row = i / width;
        let col = i % width;
        interp(input[2 * row * width + col], input[(2 * row + 1) * width + col], r)
    }).collect();
    std::hint::black_box(&output);
    if let Some(d) = directory { mark(d, "end fold"); }
    output
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some("fixture") {
        let output = fold(17, 4, None);
        let bytes: Vec<_> = output.iter().flat_map(|x| [x.c0, x.c1, x.c2]).flat_map(u64::to_le_bytes).collect();
        fs::write(&args[2], bytes).unwrap();
    } else {
        let directory = if args.len() == 4 { Some(Path::new(&args[3])) } else { None };
        let output = fold(16384, 4, directory);
        println!("fold rows=16384 width=4 sink={}", output.last().unwrap().c0);
    }
}
