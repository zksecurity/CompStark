// Copyright (c) 2026 zkSecurity. Apache-2.0.
// Observer of the unchanged production factored Basis constructor.
use super::*;

pub fn matrices() -> (Vec<F192>, Vec<F192>) {
    fn value(i: u64) -> F192 {
        F192::new(0x123456789abcdef0u64.wrapping_add(31 * i),
            0xfedcba9876543210u64.wrapping_add(i * i),
            0x8000000000000001u64.wrapping_add(17 * i))
    }
    let stack: Vec<_> = (0..4096).map(|i| F64(0x9e3779b97f4a7c15u64.wrapping_mul(i + 1))).collect();
    let claims: Vec<_> = (0..3).map(|t| StackClaim::Point {
        offset: 0,
        low_point: (0..12).map(|i| value(t * 17 + i + 101)).collect(),
        value: F192::ZERO,
    }).collect();
    let lambdas: Vec<_> = (0..3).map(|t| value(t + 501)).collect();
    let basis = initial_basis(&stack, 6, &claims, &lambdas,
        &RingSwitchOpen { offset: 0, claims: vec![] }, &[]);
    (basis.p, basis.a)
}
