// Copyright (c) 2026 zkSecurity. Apache-2.0.
// Diagnostic access to unchanged production induction kernels.
use super::*;

pub fn constants(log: usize) -> Vec<F64> { eval_sk_at_vks(log) }
pub fn dense(log: usize, constants: &[F64], queries: &[usize], weights: &[F192]) -> Vec<F192> {
    induce_basis(log, constants, queries, weights)
}
pub fn sparse(ntt: &AdditiveNttF64, log: usize, rate: usize, queries: &[usize], weights: &[F192]) -> Vec<F192> {
    transpose_forward_ntt_sparse_ext(ntt, queries, weights, log + rate, rate)
}
